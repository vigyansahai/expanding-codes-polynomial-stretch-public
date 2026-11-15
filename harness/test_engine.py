"""Proof harness regression tests. Compiler boundaries are mocked where stated."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

try:
    from harness import engine
except ImportError:
    import engine


def node(name="root", deps=()):
    result = {
        "id": name, "declaration": name, "file": name + ".lean",
        "statement": "True", "statement_sha256": engine.digest("True"),
        "status": "open", "dependencies": list(deps), "context_files": [],
        "sources": [{"path": "paper.txt", "lines": "323-330"}],
        "proof_route": "Construct a witness and check the defining property.",
        "failed_attempts": [], "owner": name + "_worker", "interface": "provisional",
        "review": {"reviewer": "coordinator", "statement_preserved": True,
                   "strictly_useful": True, "notes": "Reviewed the frozen full proposition."},
    }
    if deps:
        result["decomposition"] = {
            "parent_proof_route": "Apply the child witness lemma.",
            "children": [{"id": dep, "purpose": "Isolate the finite witness construction.",
                          "proof_route": "Enumerate the finite candidate set.",
                          "strictly_useful": "Removes the asymptotic quantifier and fixes the finite parameters."}
                         for dep in deps],
        }
    return result


def graph(*nodes):
    return {"schema_version": 1,
            "versions": {"lean": engine.LEAN_VERSION, "mathlib": engine.MATHLIB_VERSION},
            "allowed_axioms": sorted(engine.KERNEL_AXIOMS), "nodes": list(nodes or [node()])}


class StructureTests(unittest.TestCase):
    def test_valid_open_graph(self):
        self.assertEqual(set(engine.validate(graph(node("root", ["child"]), node("child")))), {"root", "child"})

    def test_cycle_and_self_dependency(self):
        for value in (graph(node("a", ["b"]), node("b", ["a"])), graph(node("a", ["a"]))):
            with self.assertRaisesRegex(engine.HarnessError, "cycle|self dependency"):
                engine.validate(value)

    def test_missing_dependency(self):
        with self.assertRaisesRegex(engine.HarnessError, "missing dependency"):
            engine.validate(graph(node("root", ["absent"])))

    def test_duplicate_and_missing_nodes(self):
        with self.assertRaisesRegex(engine.HarnessError, "duplicate node"):
            engine.validate(graph(node(), node()))
        with self.assertRaisesRegex(engine.HarnessError, "node needs id"):
            engine.validate(graph({}))

    def test_forged_proved_label(self):
        value = graph(); value["nodes"][0]["status"] = "proved"
        with self.assertRaisesRegex(engine.HarnessError, "verification receipt"):
            engine.validate(value)

    def test_hash_change(self):
        value = graph(); value["nodes"][0]["statement"] = "False"
        with self.assertRaisesRegex(engine.HarnessError, "statement hash changed"):
            engine.validate(value)

    def test_review_required(self):
        value = graph(); del value["nodes"][0]["review"]["notes"]
        with self.assertRaisesRegex(engine.HarnessError, "mandatory interface review"):
            engine.validate(value)

    def test_child_purpose_required(self):
        value = graph(node("root", ["child"]), node("child"))
        value["nodes"][0]["decomposition"]["children"][0]["purpose"] = ""
        with self.assertRaisesRegex(engine.HarnessError, "lacks purpose"):
            engine.validate(value)

    def test_no_custom_axiom_approval(self):
        value = graph(); value["allowed_axioms"].append("MyMagic")
        with self.assertRaisesRegex(engine.HarnessError, "only propext"):
            engine.validate(value)

    def test_multiple_file_owners(self):
        first, second = node("first"), node("second"); second["file"] = first["file"]
        with self.assertRaisesRegex(engine.HarnessError, "multiple workers"):
            engine.validate(graph(first, second))


class AxiomTests(unittest.TestCase):
    def test_standard_axioms_multiline(self):
        output = "warning: example\n'Foo.bar' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n"
        self.assertEqual(engine.parse_axioms(output, "Foo.bar", engine.KERNEL_AXIOMS), sorted(engine.KERNEL_AXIOMS))

    def test_no_axioms(self):
        self.assertEqual(engine.parse_axioms("'foo' does not depend on any axioms", "foo", set()), [])

    def test_sorry_and_custom_axioms_rejected(self):
        for axiom in ("sorryAx", "Project.hiddenAssumption"):
            with self.assertRaisesRegex(engine.HarnessError, "unapproved axioms"):
                engine.parse_axioms(f"'foo' depends on axioms: [{axiom}]", "foo", engine.KERNEL_AXIOMS)

    def test_wrong_constant_missing_and_ambiguous_output(self):
        for output in ("'bar' depends on axioms: []", "", "'foo' has no axioms\n'foo' has no axioms"):
            with self.assertRaisesRegex(engine.HarnessError, "missing or ambiguous"):
                engine.parse_axioms(output, "foo", engine.KERNEL_AXIOMS)


class FileTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        for filename, text in (("AGENTS.md", "No proof shortcuts."), ("lean-toolchain", engine.LEAN_VERSION),
                               ("lake-manifest.json", "{}"), ("root.lean", "theorem root : True := by trivial\n")):
            (self.root / filename).write_text(text)

    def proof_output(self, root, current):
        return f"'{current['declaration']}' does not depend on any axioms\n"

    def test_proof_and_changed_file_receipt(self):
        checked = engine.verify(graph(), self.root, "root", lean_runner=self.proof_output)
        self.assertEqual(checked["nodes"][0]["status"], "proved")
        engine.validate(checked, self.root)
        (self.root / "root.lean").write_text("theorem root : True := by decide\n")
        with self.assertRaisesRegex(engine.HarnessError, "changed verified file"):
            engine.validate(checked, self.root)

    def test_prove_rechecks_even_forged_receipt(self):
        checked = engine.verify(graph(), self.root, "root", lean_runner=self.proof_output)
        calls = []
        def reject(root, current):
            calls.append(current["id"])
            return "'root' depends on axioms: [sorryAx]"
        with self.assertRaisesRegex(engine.HarnessError, "unapproved axioms"):
            engine.verify(checked, self.root, "root", lean_runner=reject)
        self.assertEqual(calls, ["root"])

    def test_transitive_closure_rechecked(self):
        (self.root / "child.lean").write_text("theorem child : True := by trivial\n")
        value = graph(node("root", ["child"]), node("child"))
        calls = []
        def runner(root, current):
            calls.append(current["id"]); return self.proof_output(root, current)
        checked = engine.verify(value, self.root, "root", lean_runner=runner)
        self.assertEqual(calls, ["child", "root"])
        self.assertTrue(all(n["status"] == "proved" for n in checked["nodes"]))
        checked["nodes"][1]["status"] = "open"
        with self.assertRaisesRegex(engine.HarnessError, "requires proved transitive"):
            engine.validate(checked, self.root)

    def test_batch_preserves_individual_closures(self):
        (self.root / "second.lean").write_text("theorem second : True := by trivial\n")
        value = graph(node("root"), node("second"))
        checked = engine.verify_many(value, self.root, ["root", "second"], lean_runner=self.proof_output)
        self.assertEqual([n["status"] for n in checked["nodes"]], ["proved", "proved"])
        for current in checked["nodes"]:
            self.assertEqual(set(current["verification"]["closure_signatures"]), {current["id"]})
        engine.validate(checked, self.root)
        self.assertTrue(all(n["status"] == "open" for n in value["nodes"]))

    def test_batch_failure_does_not_return_partial_proof(self):
        (self.root / "second.lean").write_text("theorem second : True := by trivial\n")
        value = graph(node("root"), node("second"))
        def runner(root, current):
            if current["id"] == "second":
                return "'second' depends on axioms: [sorryAx]"
            return self.proof_output(root, current)
        with self.assertRaisesRegex(engine.HarnessError, "unapproved axioms"):
            engine.verify_many(value, self.root, ["root", "second"], lean_runner=runner)
        self.assertTrue(all(n["status"] == "open" for n in value["nodes"]))

    def test_metadata_signature_invalidation(self):
        checked = engine.verify(graph(), self.root, "root", lean_runner=self.proof_output)
        checked["nodes"][0]["proof_route"] = "Changed route."
        with self.assertRaisesRegex(engine.HarnessError, "stale task signature"):
            engine.validate(checked, self.root)

    def test_coordinator_review_before_verification(self):
        value = graph(); value["nodes"][0]["review"]["statement_preserved"] = False
        with self.assertRaisesRegex(engine.HarnessError, "coordinator must review"):
            engine.verify(value, self.root, "root", lean_runner=self.proof_output)

    def test_definition_hole_forbidden(self):
        (self.root / "root.lean").write_text("def bad : Nat := sorry\ntheorem root : True := by trivial\n")
        with self.assertRaisesRegex(engine.HarnessError, "hole is not"):
            engine.verify(graph(), self.root, "root", lean_runner=self.proof_output)

    def test_axiom_and_unsafe_source_forbidden(self):
        for source in ("axiom magic : False\n", "unsafe def bad : Nat := 0\n"):
            (self.root / "root.lean").write_text(source)
            with self.assertRaisesRegex(engine.HarnessError, "custom axiom or unsafe"):
                engine.verify(graph(), self.root, "root", lean_runner=self.proof_output)

    def test_comments_and_strings_do_not_count_as_holes(self):
        source = '/- nested /- sorry -/ axiom -/\n#check "sorry"\ntheorem root : True := by trivial\n'
        (self.root / "root.lean").write_text(source)
        checked = engine.verify(graph(), self.root, "root", lean_runner=self.proof_output)
        self.assertEqual(checked["nodes"][0]["status"], "proved")

    def test_reduction_allows_only_registered_child_hole(self):
        (self.root / "root.lean").write_text("import child\ntheorem root : True := child\n")
        (self.root / "child.lean").write_text("theorem child : True := by sorry\n")
        value = graph(node("root", ["child"]), node("child"))
        def runner(root, current):
            return f"'{current['declaration']}' depends on axioms: [sorryAx]\n"
        checked = engine.verify(value, self.root, "root", "reduction", runner)
        self.assertEqual(checked["nodes"][0]["status"], "reduction_checked")
        self.assertEqual(checked["nodes"][1]["status"], "open")
        with self.assertRaisesRegex(engine.HarnessError, "hole is not"):
            engine.verify(value, self.root, "root", "prove", runner)
        (self.root / "root.lean").write_text("import child\ntheorem root : True := by sorry\n")
        with self.assertRaisesRegex(engine.HarnessError, "hole is not"):
            engine.verify(value, self.root, "root", "reduction", runner)

    def test_ancestor_import_forbidden(self):
        (self.root / "child.lean").write_text("import root\ntheorem child : True := by trivial\n")
        with self.assertRaisesRegex(engine.HarnessError, "ancestor"):
            engine.verify(graph(node("root", ["child"]), node("child")), self.root, "root", lean_runner=self.proof_output)

    def test_import_cycle_forbidden(self):
        (self.root / "root.lean").write_text("import child\n")
        (self.root / "child.lean").write_text("import root\n")
        with self.assertRaisesRegex(engine.HarnessError, "import cycle"):
            engine.source_closure(self.root, ["root.lean"])

    def test_packet_has_agent_rules_and_forbidden_imports(self):
        (self.root / "child.lean").write_text("theorem child : True := by trivial\n")
        packet = engine.task_packet(graph(node("root", ["child"]), node("child")), self.root, "child")
        self.assertIn("AGENTS.md", packet["context"])
        self.assertEqual(packet["forbidden_ancestor_imports"], ["root.lean"])
        self.assertEqual(packet["file_ownership"]["editable"], ["child.lean"])

    def test_path_escape_forbidden(self):
        value = graph(); value["nodes"][0]["context_files"] = ["../outside"]
        with self.assertRaisesRegex(engine.HarnessError, "allowlisted|escapes project"):
            engine.validate(value, self.root)

    def test_secret_context_is_rejected_before_read(self):
        for secret_path in (".env", ".env.local", "credentials.json", ".aws/config", "secrets.txt"):
            value = graph(); value["nodes"][0]["context_files"] = [secret_path]
            # The file need not exist: reject the path before any content read.
            with self.assertRaisesRegex(engine.HarnessError, "allowlisted"):
                engine.task_packet(value, self.root, "root")

    def test_attributed_definition_hole_is_not_an_open_theorem(self):
        (self.root / "root.lean").write_text("theorem root : True := by trivial\n")
        (self.root / "child.lean").write_text("theorem child : True := by sorry\n@[simp] def bad : Nat := sorry\n")
        with self.assertRaisesRegex(engine.HarnessError, "hole is not"):
            engine.verify(graph(node("root", ["child"]), node("child")), self.root, "root", "reduction", self.proof_output)

    def test_multiple_imports_are_tracked(self):
        self.assertEqual(engine.imports_of("import Foo.Bar Baz\npublic import Quux -- comment\n"), ["Foo.Bar", "Baz", "Quux"])

    def test_build_is_run_before_actual_audit(self):
        events = []
        with patch.object(engine, "check_versions", side_effect=lambda _: events.append("versions")), \
             patch.object(engine, "build_modules", side_effect=lambda *_: events.append("build")), \
             patch.object(engine, "audit_declaration", side_effect=lambda root, n: events.append("audit") or self.proof_output(root, n)):
            engine.verify(graph(), self.root, "root")
        self.assertEqual(events, ["versions", "build", "audit"])

    def test_batch_audit_checks_each_type_and_axiom_set_once(self):
        captured = []
        def fake_lean(root, args):
            captured.append((root / args[0]).read_text())
            return "audit output"
        with patch.object(engine, "run_lean", side_effect=fake_lean):
            result = engine.audit_declarations(self.root, [node("root"), node("child")])
        self.assertEqual(result, "audit output")
        self.assertEqual(len(captured), 1)
        self.assertIn("import root", captured[0])
        self.assertIn("import child", captured[0])
        self.assertIn("#print axioms root", captured[0])
        self.assertIn("#print axioms child", captured[0])
        self.assertEqual(captured[0].count("example :"), 2)

    def test_same_module_helpers_must_precede_parent(self):
        value = graph(node("root", ["child"]), node("child"))
        value["nodes"][1]["file"] = "root.lean"
        (self.root / "root.lean").write_text(
            "theorem child : True := by trivial\ntheorem root : True := by exact child\n")
        engine.scan_sources(value, engine.node_map(value), self.root, "root", "prove")
        (self.root / "root.lean").write_text(
            "theorem root : True := by trivial\ntheorem child : True := by trivial\n")
        with self.assertRaisesRegex(engine.HarnessError, "before its ancestor"):
            engine.scan_sources(value, engine.node_map(value), self.root, "root", "prove")

    def test_unused_registered_import_hole_requires_clean_axiom_audit(self):
        (self.root / "root.lean").write_text("import child\ntheorem root : True := by trivial\n")
        (self.root / "child.lean").write_text("theorem child : True := by sorry\n")
        value = graph(node("root"), node("child"))
        checked = engine.verify(value, self.root, "root", "prove", self.proof_output)
        self.assertEqual(checked["nodes"][0]["status"], "proved")
        self.assertEqual(checked["nodes"][1]["status"], "open")
        def contaminated(_root, current):
            return f"'{current['declaration']}' depends on axioms: [sorryAx]"
        with self.assertRaisesRegex(engine.HarnessError, "unapproved axioms"):
            engine.verify(value, self.root, "root", "prove", contaminated)


if __name__ == "__main__":
    unittest.main()
