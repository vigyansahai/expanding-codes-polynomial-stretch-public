#!/usr/bin/env python3
"""Small, local, coordinator-driven Lean proof DAG harness (Python standard library)."""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from datetime import datetime, timezone

LEAN_VERSION = "leanprover/lean4:v4.33.1"
MATHLIB_VERSION = "0df444a360eaa60ab8c11dca51a86af692955474"
KERNEL_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
STATUSES = {"open", "reduction_checked", "proved"}
IDENT = r"[A-Za-z_][A-Za-z_0-9'.]*(?:\.[A-Za-z_][A-Za-z_0-9']*)*"


class HarnessError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise HarnessError(message)


def digest(value):
    if not isinstance(value, str):
        value = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(value.encode()).hexdigest()


def nonempty(value):
    return isinstance(value, str) and bool(value.strip())


def local_path(root, name):
    require(isinstance(name, str) and bool(name), "file path must be a nonempty string")
    path = (root / name).resolve()
    require(path.is_relative_to(root.resolve()), f"file escapes project: {name}")
    require(path.is_file(), f"missing file: {name}")
    return path


def check_context_path(name):
    require(isinstance(name, str), "context file path must be text")
    path = Path(name)
    require(path.suffix.lower() in {".lean", ".md", ".txt", ".json", ".toml"}
            and not any(p.startswith(".") and p != "." for p in path.parts)
            and not re.search(r"(?:^|[._/-])(?:secrets?|credentials?|tokens?|id_rsa|id_ed25519)(?:[._/-]|$)", name, re.I),
            f"context path is not an allowlisted proof/document artifact: {name}")


def strip_comments_strings(source):
    """Mask nested Lean comments and ordinary strings, preserving offsets/newlines.

    This is deliberately not a Lean parser. Quoted identifiers, custom syntax,
    macros, quotations and generated declarations require human interface review.
    """
    out = list(source)
    i, depth, string = 0, 0, False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                out[i:i + 2] = "  "; depth += 1; i += 2
            elif source.startswith("-/", i):
                out[i:i + 2] = "  "; depth -= 1; i += 2
            else:
                if source[i] != "\n": out[i] = " "
                i += 1
        elif string:
            if source[i] == "\\":
                out[i] = " "
                if i + 1 < len(source) and source[i + 1] != "\n": out[i + 1] = " "
                i += 2
            else:
                if source[i] != "\n": out[i] = " "
                if source[i] == '"': string = False
                i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            if end < 0: end = len(source)
            out[i:end] = " " * (end - i); i = end
        elif source.startswith("/-", i):
            out[i:i + 2] = "  "; depth = 1; i += 2
        elif source[i] == '"':
            out[i] = " "; string = True; i += 1
        else:
            i += 1
    require(not depth and not string, "unterminated Lean comment or string")
    return "".join(out)


def node_map(graph):
    nodes = graph.get("nodes")
    require(isinstance(nodes, list), "nodes must be a list")
    result = {}
    for node in nodes:
        require(isinstance(node, dict), "node must be an object")
        name = node.get("id")
        require(nonempty(name), "node needs id")
        require(name not in result, f"duplicate node id: {name}")
        result[name] = node
    return result


def closure(nodes, node_id):
    visiting, done, order = set(), set(), []
    def visit(name):
        require(name in nodes, f"missing dependency: {name}")
        require(name not in visiting, f"dependency cycle through {name}")
        if name in done: return
        visiting.add(name)
        for child in nodes[name].get("dependencies", []): visit(child)
        visiting.remove(name); done.add(name); order.append(name)
    visit(node_id)
    return order


def node_signature(node):
    """Status/receipts are excluded; all proof-task and review metadata is frozen."""
    return digest({k: v for k, v in node.items() if k not in {"status", "verification"}})


def validate(graph, root=None, check_receipts=True):
    require(graph.get("schema_version") == 1, "schema_version must be 1")
    require(graph.get("versions") == {"lean": LEAN_VERSION, "mathlib": MATHLIB_VERSION},
            "versions must match pinned Lean and mathlib")
    allowed = graph.get("allowed_axioms", sorted(KERNEL_AXIOMS))
    require(isinstance(allowed, list) and set(allowed) <= KERNEL_AXIOMS,
            "only propext, Classical.choice, Quot.sound may be approved")
    nodes = node_map(graph)
    declarations, owners = set(), {}
    for name, node in nodes.items():
        for field in ("declaration", "file", "statement", "proof_route", "owner"):
            require(nonempty(node.get(field)), f"{name}: missing {field}")
        require(re.fullmatch(IDENT, node["declaration"]), f"{name}: unsupported declaration name")
        require(node["declaration"] not in declarations, f"duplicate declaration: {node['declaration']}")
        declarations.add(node["declaration"])
        require(node["file"].endswith(".lean"), f"{name}: file must end in .lean")
        require(node["statement_sha256"] == digest(node["statement"]), f"{name}: statement hash changed")
        require(node.get("status") in STATUSES, f"{name}: invalid status")
        require(node.get("interface") in {"provisional", "canonical"}, f"{name}: interface must be explicit")
        deps = node.get("dependencies")
        require(isinstance(deps, list) and all(isinstance(d, str) for d in deps), f"{name}: invalid dependencies")
        require(len(deps) == len(set(deps)), f"{name}: duplicate dependency")
        require(name not in deps, f"{name}: self dependency")
        for field in ("context_files", "sources", "failed_attempts"):
            require(isinstance(node.get(field), list), f"{name}: missing list {field}")
        require(all(isinstance(p, str) for p in node["context_files"]), f"{name}: invalid context files")
        for context_file in node["context_files"]: check_context_path(context_file)
        review = node.get("review", {})
        require(all(k in review for k in ("reviewer", "statement_preserved", "strictly_useful", "notes")),
                f"{name}: missing mandatory interface review")
        require(nonempty(review["reviewer"]) and nonempty(review["notes"]), f"{name}: review needs reviewer and notes")
        require(type(review["statement_preserved"]) is bool and type(review["strictly_useful"]) is bool,
                f"{name}: review flags must be booleans")
        if node["status"] != "open":
            require(review["statement_preserved"] is True, f"{name}: statement review incomplete")
        if deps:
            decomposition = node.get("decomposition", {})
            require(nonempty(decomposition.get("parent_proof_route")), f"{name}: missing parent proof route")
            children = decomposition.get("children", [])
            require(isinstance(children, list) and all(isinstance(c, dict) for c in children), f"{name}: invalid child metadata")
            require(len(children) == len(deps) and {c.get("id") for c in children} == set(deps),
                    f"{name}: decomposition children must equal dependencies")
            for child in children:
                for field in ("purpose", "proof_route", "strictly_useful"):
                    require(nonempty(child.get(field)), f"{name}: child {child.get('id')} lacks {field}")
            if node["status"] != "open":
                require(review["strictly_useful"] is True, f"{name}: decomposition usefulness review incomplete")
        require(node["file"] not in owners or owners[node["file"]] == node["owner"],
                f"{name}: multiple workers own {node['file']}")
        owners[node["file"]] = node["owner"]
        if root is not None:
            local_path(root, node["file"])
            for path in node["context_files"]: local_path(root, path)
    for name in nodes: closure(nodes, name)
    if check_receipts:
        for name, node in nodes.items():
            if node["status"] == "open": continue
            receipt = node.get("verification", {})
            require(receipt.get("mode") == ("prove" if node["status"] == "proved" else "reduction"),
                    f"{name}: status has no matching verification receipt; run verify")
            require(receipt.get("signature_sha256") == node_signature(node), f"{name}: stale task signature")
            expected = {n: node_signature(nodes[n]) for n in closure(nodes, name)}
            require(receipt.get("closure_signatures") == expected, f"{name}: stale dependency closure")
            require(isinstance(receipt.get("files"), dict) and receipt["files"], f"{name}: missing file manifest")
            require(receipt.get("signature_check") == "Lean full type compatibility with @declaration",
                    f"{name}: missing Lean statement check")
            parse_axioms(receipt.get("axiom_output", ""), node["declaration"],
                         set(allowed) | ({"sorryAx"} if node["status"] == "reduction_checked" else set()))
            if node["status"] == "proved":
                require(all(nodes[d]["status"] == "proved" for d in node["dependencies"]),
                        f"{name}: proved status requires proved transitive dependencies")
            if root is not None:
                for path, old_hash in receipt["files"].items():
                    require(digest(local_path(root, path).read_text()) == old_hash, f"{name}: changed verified file: {path}")
    return nodes


def imports_of(source):
    masked = strip_comments_strings(source)
    imports = list(re.finditer(r"(?m)^[ \t]*(?:public[ \t]+)?import[ \t]+([^\n]+)", masked))
    require(len(imports) == len(re.findall(r"\bimport\b", masked)),
            "unsupported import syntax; use one or more module names on an import line")
    modules = []
    for match in imports:
        names = match.group(1).split()
        require(names and all(re.fullmatch(IDENT, name) for name in names), "unsupported import module name")
        modules.extend(names)
    return modules


def source_closure(root, initial):
    """Track project-local imports; external packages are pinned separately."""
    root = root.resolve()
    contents = {}
    def visit(filename, stack):
        path = local_path(root, filename)
        key = str(path.relative_to(root))
        require(key not in stack, f"local import cycle: {' -> '.join([*stack, key])}")
        if key in contents: return
        source = path.read_text()
        contents[key] = source
        for module in imports_of(source):
            imported = root.joinpath(*module.split(".")).with_suffix(".lean")
            if imported.is_file(): visit(str(imported.relative_to(root)), [*stack, key])
    for filename in initial: visit(filename, [])
    return contents


def scan_sources(graph, nodes, root, target, mode):
    reachable = set(closure(nodes, target))
    initial = [nodes[n]["file"] for n in reachable]
    initial += [p for n in reachable for p in nodes[n]["context_files"] if p.endswith(".lean")]
    contents = source_closure(root, initial)
    for child in reachable:
        child_files = source_closure(root, [nodes[child]["file"]])
        for ancestor in reachable:
            if child == ancestor or child not in closure(nodes, ancestor)[:-1]: continue
            ancestor_file = nodes[ancestor]["file"]
            if ancestor_file == nodes[child]["file"]:
                # Grouped, already checked helper modules are legitimate. Lean
                # declaration order prevents forward reference to an ancestor.
                masked = strip_comments_strings(contents[ancestor_file])
                def position(task):
                    full = re.escape(task["declaration"])
                    short = re.escape(task["declaration"].split(".")[-1])
                    matches = list(re.finditer(r"\b(?:theorem|lemma)\s+(?:" + full + "|" + short + r")(?=[\s({:\[])", masked))
                    require(len(matches) == 1, f"{task['id']}: ambiguous same-module declaration order")
                    return matches[0].start()
                require(position(nodes[child]) < position(nodes[ancestor]),
                        f"{child}: same-module helper must be declared before its ancestor {ancestor}")
            else:
                require(ancestor_file not in child_files,
                        f"{child}: imports target/ancestor file {ancestor_file}")
    # A deliberately conservative lexical gate, followed by Lean compilation and
    # kernel axiom inspection. It is not a security sandbox for hostile Lean code.
    command = re.compile(r"\b(theorem|lemma|def|abbrev|opaque|instance|structure|inductive|axiom|unsafe|example|initialize|syntax|macro|elab|notation|namespace|section|end|variable)\b(?:\s+(" + IDENT + r"))?|(?m:^[ \t]*(#[A-Za-z_]+))")
    for filename, source in contents.items():
        masked = strip_comments_strings(source)
        require(not re.search(r"\baxiom\b|\bunsafe\b", masked), f"{filename}: custom axiom or unsafe declaration forbidden")
        declarations = list(command.finditer(masked))
        for hole in re.finditer(r"\b(?:sorry|admit|sorryAx)\b", masked):
            require(hole.group() != "sorryAx", f"{filename}: direct sorryAx references forbidden")
            before = [d for d in declarations if d.start() < hole.start()]
            require(before, f"{filename}: unclassified proof hole")
            declaration = before[-1]
            kind, short_name = declaration.group(1), declaration.group(2)
            body_start = masked.find(":=", declaration.end(), hole.start())
            candidates = [n for n in nodes.values() if n["file"] == filename
                          and n["declaration"].split(".")[-1] == short_name]
            permitted = len(candidates) == 1 and candidates[0]["id"] != target and candidates[0]["status"] == "open" and (
                (mode == "reduction" and candidates[0]["id"] in reachable) or
                (mode == "prove" and candidates[0]["id"] not in reachable))
            # A proved helper may import a module that also contains unrelated,
            # registered open theorems. Its own transitive axiom audit must still
            # exclude sorryAx, so none of those placeholders can be used.
            require(permitted and kind in {"theorem", "lemma"} and body_start >= 0,
                    f"{filename}: hole is not a registered reachable open child theorem body")
    return contents


def parse_axioms(output, declaration, allowed):
    """Accept only a recognized #print axioms result naming the requested constant."""
    require(isinstance(output, str), "axiom output must be text")
    name = re.escape(declaration)
    pattern = rf"['‘]({name})['’]\s+(?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms|has no axioms))"
    matches = list(re.finditer(pattern, output, re.S))
    require(len(matches) == 1, f"missing or ambiguous #print axioms output for {declaration}")
    body = matches[0].group(2)
    axioms = [] if body is None else [a.strip() for a in body.split(",") if a.strip()]
    require(all(re.fullmatch(IDENT, a) for a in axioms), "unrecognized axiom output")
    forbidden = set(axioms) - set(allowed)
    require(not forbidden, f"unapproved axioms: {', '.join(sorted(forbidden))}")
    return sorted(set(axioms))


def run_lean(root, args):
    serial = root / "tools/lake-serial"
    lake = str(serial) if serial.is_file() else (shutil.which("lake") or str(Path.home() / ".elan/bin/lake"))
    result = subprocess.run([lake, "env", "lean", "-DautoImplicit=false", *args],
                            cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    require(result.returncode == 0, f"Lean failed ({result.returncode}):\n{result.stdout}")
    return result.stdout


def build_modules(root, files):
    serial = root / "tools/lake-serial"
    lake = str(serial) if serial.is_file() else (shutil.which("lake") or str(Path.home() / ".elan/bin/lake"))
    modules = []
    for filename in files:
        parts = Path(filename).with_suffix("").parts
        require(all(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9']*", p) for p in parts),
                f"unsupported module file name: {filename}")
        modules.append(".".join(parts))
    result = subprocess.run([lake, "build", *dict.fromkeys(modules)], cwd=root, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    require(result.returncode == 0, f"Lake build failed ({result.returncode}):\n{result.stdout}")
    return result.stdout


def check_versions(root):
    require(local_path(root, "lean-toolchain").read_text().strip() == LEAN_VERSION, "Lean toolchain changed")
    manifest = json.loads(local_path(root, "lake-manifest.json").read_text())
    packages = [p for p in manifest.get("packages", []) if p.get("name") == "mathlib"]
    require(len(packages) == 1 and packages[0].get("rev") == MATHLIB_VERSION, "mathlib manifest revision changed")
    platform_manifest = root / "harness/platform/definition-manifest.json"
    if platform_manifest.is_file():
        for entry in json.loads(platform_manifest.read_text()):
            require(digest(local_path(root, entry["path"]).read_text()) == entry["sha256"],
                    f"frozen platform definition changed: {entry['path']}")
    mathlib = root / ".lake/packages/mathlib"
    for args, expected, message in (
            (["rev-parse", "HEAD"], MATHLIB_VERSION, "mathlib checkout revision changed"),
            (["status", "--porcelain", "--untracked-files=no"], "", "mathlib tracked files modified")):
        result = subprocess.run(["git", "-C", str(mathlib), *args], text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        require(result.returncode == 0 and result.stdout.strip() == expected, message)
    version = run_lean(root, ["--version"])
    require("version 4.33.1" in version, "executed Lean version is not 4.33.1")


def audit_declaration(root, node):
    # Appending to the actual source avoids silently importing stale local oleans.
    # Each closure node is independently checked with its current source text.
    source = local_path(root, node["file"]).read_text()
    audit = (source + "\n\nset_option autoImplicit false\nopen scoped Classical BigOperators\n"
             + f"example : ({node['statement']}) := @{node['declaration']}\n"
             + f"#print axioms {node['declaration']}\n")
    handle, temporary = tempfile.mkstemp(prefix="proof_audit_", suffix=".lean", dir=root)
    try:
        with os.fdopen(handle, "w") as stream: stream.write(audit)
        return run_lean(root, [str(Path(temporary).relative_to(root))])
    finally:
        Path(temporary).unlink(missing_ok=True)


def audit_declarations(root, nodes):
    """Audit a freshly built closure in one fresh Lean process.

    Lake must already have rebuilt the current sources. This shares import work,
    not proof assumptions: every proposition and transitive axiom set is checked.
    """
    modules = list(dict.fromkeys(".".join(Path(n["file"]).with_suffix("").parts) for n in nodes))
    source = "\n".join("import " + m for m in modules)
    source += "\nset_option autoImplicit false\nopen scoped Classical BigOperators\n"
    for node in nodes:
        source += f"example : ({node['statement']}) := @{node['declaration']}\n"
        source += f"#print axioms {node['declaration']}\n"
    handle, temporary = tempfile.mkstemp(prefix="closure_audit_", suffix=".lean", dir=root)
    try:
        with os.fdopen(handle, "w") as stream:
            stream.write(source)
        return run_lean(root, [str(Path(temporary).relative_to(root))])
    finally:
        Path(temporary).unlink(missing_ok=True)


def verify(graph, root, target, mode="prove", lean_runner=None):
    """Recheck the entire closure; receipts alone never establish a proof."""
    nodes = validate(graph, root, check_receipts=False)
    require(target in nodes, f"unknown node: {target}")
    require(mode in {"prove", "reduction"}, "invalid verification mode")
    if lean_runner is None: check_versions(root)
    order = closure(nodes, target)
    require(mode != "reduction" or nodes[target]["dependencies"], "a reduction must have child dependencies")
    for name in order:
        review = nodes[name]["review"]
        # Open children may remain unreviewed in a reduction, but the checked
        # reduction itself and every claimed proof require coordinator review.
        if mode == "prove" or name == target:
            require(review["statement_preserved"], f"{name}: coordinator must review exact statement")
            if nodes[name]["dependencies"]:
                require(review["strictly_useful"], f"{name}: coordinator must review decomposition usefulness")
    candidate = copy.deepcopy(graph)
    updated = node_map(candidate)
    allowed = set(graph.get("allowed_axioms", sorted(KERNEL_AXIOMS)))
    runner = lean_runner or audit_declaration
    # Check all source before executing Lean, then let Lake rebuild the actual
    # module import graph. An audit-only `lean file` could accept stale oleans.
    reduction_contents = scan_sources(candidate, updated, root, target, mode)
    if lean_runner is None:
        build_modules(root, [updated[n]["file"] for n in order])
        if len(order) > 1:
            batch_output = audit_declarations(root, [updated[n] for n in order])
            runner = lambda _root, _node: batch_output
    for name in order:
        node = updated[name]
        contents = reduction_contents if mode == "reduction" else scan_sources(candidate, updated, root, name, mode)
        # In reduction mode check each open child source directly, allowing its
        # own registered open body only in this auxiliary compilation. Its
        # declaration axiom output remains recorded only for the target.
        output = runner(root, node)
        axioms = parse_axioms(output, node["declaration"], allowed | ({"sorryAx"} if mode == "reduction" else set()))
        if mode == "reduction" and name != target: continue
        manifest = {p: digest(s) for p, s in contents.items()}
        for context in ["AGENTS.md", "lean-toolchain", "lake-manifest.json"] + [p for n in closure(updated, name) for p in updated[n]["context_files"]]:
            manifest[context] = digest(local_path(root, context).read_text())
        node["status"] = "proved" if mode == "prove" else "reduction_checked"
        node["verification"] = {
            "mode": mode,
            "checked_at": datetime.now(timezone.utc).isoformat(),
            "signature_sha256": node_signature(node),
            "closure_signatures": {n: node_signature(updated[n]) for n in closure(updated, name)},
            "files": manifest,
            "axioms": axioms,
            "axiom_output": output,
            "signature_check": "Lean full type compatibility with @declaration",
            "trust_note": "Freshness record, not a security certificate; verify always reruns Lean.",
        }
    validate(candidate, root)
    return candidate


def verify_many(graph, root, targets, lean_runner=None):
    """Verify several proof closures with one fresh build and one Lean audit.

    Each target keeps its own dependency closure and receipt. This only shares
    compiler startup/import work; every declaration is still checked by Lean.
    The caller writes the graph only after all targets have passed.
    """
    require(isinstance(targets, list) and targets, "batch verification needs targets")
    require(len(targets) == len(set(targets)), "duplicate batch verification target")
    nodes = validate(graph, root, check_receipts=False)
    for target in targets:
        require(target in nodes, f"unknown node: {target}")
        scan_sources(graph, nodes, root, target, "prove")
    order = list(dict.fromkeys(name for target in targets for name in closure(nodes, target)))
    for name in order:
        review = nodes[name]["review"]
        require(review["statement_preserved"], f"{name}: coordinator must review exact statement")
        if nodes[name]["dependencies"]:
            require(review["strictly_useful"], f"{name}: coordinator must review decomposition usefulness")
    if lean_runner is None:
        check_versions(root)
        build_modules(root, [nodes[name]["file"] for name in order])
        output = audit_declarations(root, [nodes[name] for name in order])
        lean_runner = lambda _root, _node: output
    candidate = graph
    for target in targets:
        candidate = verify(candidate, root, target, "prove", lean_runner=lean_runner)
    return candidate


def task_packet(graph, root, target):
    nodes = validate(graph, root)
    require(target in nodes, f"unknown node: {target}")
    ancestors = [name for name in nodes if name != target and target in closure(nodes, name)]
    node = copy.deepcopy(nodes[target])
    files = list(dict.fromkeys(["AGENTS.md", node["file"], *node["context_files"]]))
    context = {p: local_path(root, p).read_text() for p in files}
    context_limit = 32000
    return {
        "node": node,
        "versions": graph["versions"],
        "file_ownership": {"editable": [node["file"]], "owner": node["owner"],
                           "scratch_directory": "harness/attempts/" + re.sub(r"[^A-Za-z0-9_-]", "_", target)},
        "forbidden_ancestor_imports": sorted({nodes[n]["file"] for n in ancestors}),
        "dependencies": [{"id": d, "declaration": nodes[d]["declaration"], "file": nodes[d]["file"],
                          "statement": nodes[d]["statement"], "statement_sha256": nodes[d]["statement_sha256"],
                          "status": nodes[d]["status"]} for d in node["dependencies"]],
        "imports": imports_of(local_path(root, node["file"]).read_text()),
        "context": {p: text if p == "AGENTS.md" else text[:context_limit] for p, text in context.items()},
        "context_manifest": {p: {"sha256": digest(text), "characters": len(text),
                                  "included_characters": len(text) if p == "AGENTS.md" else min(len(text), context_limit),
                                  "truncated": p != "AGENTS.md" and len(text) > context_limit} for p, text in context.items()},
        "instructions": (Path(__file__).with_name("worker_prompt.txt")).read_text(),
    }


def write_json(path, data):
    path = Path(path)
    fd, temporary = tempfile.mkstemp(prefix=path.name + ".", dir=path.parent)
    try:
        with os.fdopen(fd, "w") as stream:
            json.dump(data, stream, indent=2, ensure_ascii=False); stream.write("\n")
        os.replace(temporary, path)
    finally:
        Path(temporary).unlink(missing_ok=True)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, epilog=(
        "Limits: lexical checks are conservative, not a full Lean parser or hostile-code sandbox. "
        "Use ordinary named theorem/lemma declarations; custom syntax, macros, quotations, generated "
        "declarations and namespace ambiguity require coordinator review. A signature hash freezes "
        "metadata; Lean checks full type compatibility, and human review preserves the intended interface. "
        "Receipts are unauthenticated freshness records. validate checks records; verify always reruns "
        "Lean for the closure. No automatic semantic-equivalence or decomposition-usefulness claim. "
        "Coordinator dispatches bounded workers externally; this CLI never invokes model APIs."))
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--graph", type=Path, default=Path("harness/graph.json"))
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("validate")
    hash_parser = sub.add_parser("hash", help="SHA256 of exact statement text, without normalization")
    hash_parser.add_argument("file", type=Path, help="statement text file; trailing newlines count")
    packet = sub.add_parser("packet")
    packet.add_argument("node"); packet.add_argument("--output", type=Path)
    check = sub.add_parser("verify")
    check.add_argument("node"); check.add_argument("--mode", choices=("prove", "reduction"), default="prove")
    batch = sub.add_parser("verify-many", help="prove several closures with one fresh compiler audit")
    batch.add_argument("nodes", nargs="+")
    register = sub.add_parser("register", help="add an open node; existing signatures cannot be silently changed")
    register.add_argument("node_file", type=Path)
    args = parser.parse_args(argv)
    try:
        if args.command == "hash":
            print(digest(args.file.read_text())); return 0
        root = args.root.resolve()
        graph_path = args.graph if args.graph.is_absolute() else root / args.graph
        graph = json.loads(graph_path.read_text())
        if args.command == "validate":
            nodes = validate(graph, root)
            print(f"Valid graph: {len(nodes)} nodes. Receipts are records; verify reruns Lean.")
        elif args.command == "packet":
            result = task_packet(graph, root, args.node)
            if args.output: write_json(args.output, result)
            else: print(json.dumps(result, indent=2, ensure_ascii=False))
        elif args.command == "register":
            validate(graph, root)
            node = json.loads(args.node_file.read_text())
            require(node.get("status") == "open" and "verification" not in node, "register accepts only open, unverified tasks")
            require(node.get("id") not in node_map(graph), "existing node is frozen; coordinator must explicitly review graph revisions")
            graph["nodes"].append(node); validate(graph, root); write_json(graph_path, graph)
            print(f"Registered {node['id']}")
        elif args.command == "verify-many":
            graph = verify_many(graph, root, args.nodes)
            write_json(graph_path, graph)
            print(f"{', '.join(args.nodes)}: proved; current closures independently checked")
        else:
            graph = verify(graph, root, args.node, args.mode)
            write_json(graph_path, graph)
            print(f"{args.node}: {node_map(graph)[args.node]['status']}; current closure independently checked")
        return 0
    except (HarnessError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print(f"harness: {error}", file=sys.stderr); return 1


if __name__ == "__main__":
    sys.exit(main())
