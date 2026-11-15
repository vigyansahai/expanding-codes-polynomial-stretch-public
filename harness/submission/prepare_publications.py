#!/usr/bin/env python3
"""Prepare public API payloads from the checked runtime export (no network)."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
RUNTIME = ROOT / 'runtime'
ENV = '0df444a360eaa60ab8c11dca51a86af692955474'
TAGS = ['expanding-codes-polynomial-stretch', 'coding-theory', 'complexity-theory']
ORIGIN = ('Isaac M Hair and Amit Sahai, Expanding Codes with Polynomial Stretch, '
    'user-supplied 824.pdf, Section 2, Theorem 2.1 (pp. 7-9), '
    'https://prove2.me/missions/Expanding_Codes_with_Polynomial_Stretch. '
    'Machine-level implementation details were developed in the accompanying Lean formalization; '
    'the checked local proof archive has SHA256 '
    '694ed62f8511cd5a41c6354a96349e0a72f820296592e4f312215e403a2722d5.')


def save(name, payload):
    destination = ROOT / name
    destination.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + '\n')
    return {'path': str(destination.relative_to(ROOT)),
        'sha256': hashlib.sha256(destination.read_bytes()).hexdigest()}


def main():
    source = RUNTIME / 'staged/Definitions/Def_ExpandingCodes_PolynomialStretch_BinaryRuntime.lean'
    definition = {
        'definition_name': 'ExpandingCodes_PolynomialStretch_BinaryRuntime',
        'definition_title': 'Binary-field and finite-program interfaces for expanding codes',
        'definition': source.read_text(),
        'natural_language_statement': (
            'Foundational data for the computational construction in Theorem 2.1. '
            'For a positive binary extension degree $\\ell$, field elements are represented by binary '
            'coefficient vectors modulo a specified monic irreducible polynomial of degree $\\ell$. '
            'This fixes the field operations, its finite ordering, and the row geometry.\n\n'
            'The finite-program interfaces specify registers, work-tape stores, instructions, '
            'configurations, execution, and concrete program factories for parameter setup, '
            'sampling, Gram-matrix construction, and elimination. Auxiliary predicates describe '
            'their states and polynomial envelopes. The two implementation predicates require a '
            'single finite machine and a polynomial bound, chosen before the input size, with '
            'the exact output or sampling law required by the mission.\n\n'
            '**Formalization Note.** This file provides data, defining validity proofs and '
            'constructor APIs. The sampler and tester execution, correctness, and polynomial-time '
            'implementation theorems are separate proof submissions.'),
        'source': ORIGIN + ' See Section 2.1, equations (1)-(4), and Section 2.2, equation (5).',
        'tags': TAGS, 'env': ENV, 'private': False}
    manifest = {'definition_source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
        'definition': save('runtime-definition-payload.json', definition), 'problems': {}}
    problems = []
    for kind in ['sampler', 'tester']:
        metadata = json.loads((RUNTIME / (kind + '-metadata.json')).read_text())
        problem = {key: metadata[key] for key in ['theorem_name', 'formal_statement', 'preamble']}
        if kind == 'sampler':
            problem.update(
                theorem_title='One finite polynomial-time machine for the exact expanding-code sampler',
                natural_language_statement=(
                    'Let $0<\\theta<1/2$ be rational and use the specified binary-field geometry '
                    'in dimension $d=\\mathrm{dimension}(\\theta)$. There are one finite probabilistic '
                    'machine $S$, integers $A>0$, $a\\geq0$, and $N\\geq2$, depending on $\\theta$ '
                    'and independent of the input size, such that for every $n\\geq N$, every '
                    'random tape of length $T(n)=A(n+1)^a$ makes $S$ output a generator matrix '
                    'within $T(n)$ steps. For uniform independent tape bits its output law is exactly\n\n'
                    '$$\\Pr[S(n)=G]=P_{\\theta,n}(G).$$\n\n'
                    'Here $P_{\\theta,n}$ is the canonical distribution obtained by two independent '
                    'random linear forms for each layer and each value of its fixed first linear '
                    'form, together with independent uniform layer hash tables and the specified matrix encoding. '
                    'This supplies the operational sampling clauses of the efficient-family theorem.'),
                source=ORIGIN + ' Section 2.1, equations (1)-(4), pp. 8-9; '
                    'formal implementation endpoint ExpandingCodes/Computation/SamplerImplementation.lean, '
                    'binary_sampler_implementation_source.')
        else:
            problem.update(
                theorem_title='One finite polynomial-time machine for the expanding-code rank test',
                natural_language_statement=(
                    'Let $0<\\theta<1/2$ be rational and use the specified binary-field geometry '
                    'in dimension $d=\\mathrm{dimension}(\\theta)$. There are one finite deterministic '
                    'machine $D$, integers $B>0$, $b\\geq0$, and $N\\geq2$, depending on $\\theta$ '
                    'and independent of the input size and received word, such that for every '
                    '$n\\geq N$ and binary word $y$ of length $m=\\mathrm{rowCount}(d,n)$,\n\n'
                    '$$D(n,y)=\\mathrm{rankTest}_{\\theta}(y) '
                    '\\quad\\text{within }B(m+n+1)^b\\text{ steps}.$$\n\n'
                    'The test is the canonical finite-field Gram-matrix rank predicate, with its '
                    'specified row ordering and input/output encodings. This supplies the '
                    'operational deterministic-testing clause of the efficient-family theorem.'),
                source=ORIGIN + ' Section 2.2, equation (5) and the following displayed rank test, p. 9; '
                    'formal implementation endpoint ExpandingCodes/Computation/TesterImplementation.lean, '
                    'binary_tester_implementation_source.')
        problem['tags'] = TAGS
        problems.append(problem)
        manifest['problems'][kind] = {'theorem_name': problem['theorem_name']}
    manifest['problem_batch'] = save('runtime-problems-payload.json',
        {'problems': problems, 'env': ENV, 'private': False})
    save('publication-payload-manifest.json', manifest)
    print(json.dumps(manifest, indent=2))


if __name__ == '__main__':
    main()
