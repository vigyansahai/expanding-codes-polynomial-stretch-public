#!/usr/bin/env python3
"""Prepare public metadata for the checked, meaningful runtime theorem cuts."""
import hashlib
import json
from pathlib import Path

BASE = Path(__file__).resolve().parent
ENV = '0df444a360eaa60ab8c11dca51a86af692955474'
TAG = 'expanding-codes-polynomial-stretch'

TEXT = {
    'tape_compile': r'''Let $P$ be a finite source program with $R$ registers, $B$ buffers and $L$ instruction labels. Let $I$ be any input, $O$ any oracle, and $t$ a natural number. If the source execution halts after $t$ instructions with binary output $w$, its compiled canonical machine satisfies

$$\operatorname{compile}(P)(I,O)\downarrow w
\quad\text{within }1+2t\text{ machine steps}.$$

The output uses the canonical bit-to-symbol encoding. This theorem supplies a uniform, constant-overhead bridge from finite source executions to the machine model used by the expanding-code mission.''',
    'field_setup': r'''Let $\ell>0$, $q=2^\ell$, and let $s$ be a source-machine store with $R$ registers and $B$ buffers. Let $r$ injectively place a 32-register workspace in its register bank, and let $I$ be any input. Initially every register is at most $M$, workspace registers 20 and 23 contain $\ell$ and $q$, and

$$3\ell+1\le M,\qquad 2q\le M,\qquad q^2\le M.$$

The field-setup program reaches its specified final store and the canonical binary-field environment in time

$$t\le 40000(M+1)^7.$$

All registers remain at most $M$. Registers outside the workspace and the read heads, buffer contents, buffer heads and output are preserved. This provides field construction from runtime size parameters for both the sampler and the tester.''',
    'field_multiply': r'''Let $\ell>0$ and $q=2^\ell$. Encode polynomials of degree below $\ell$ by integers below $q$. Let $a,b$ be two such encodings and let $\mu<q$ encode the lower coefficients of a monic polynomial $p_\mu$ of degree $\ell$. No irreducibility assumption on $p_\mu$ is required.

Let $s$ be a store with $R$ registers and $B$ buffers, $r$ an injective placement of a 27-register workspace, and $I$ any input. Assume $M\ge1$, all registers are at most $M$, and workspace registers $0,1,3,19,23,24$ contain $a,b,q+\mu,3\ell+1,q,q^2$, respectively. The multiplication program halts with

$$t\le10000(M+1)^6,\qquad
s'[r(20)]=\operatorname{enc}\bigl(a(X)b(X)\bmod p_\mu(X)\bigr).$$

Its entire final store is the specified multiplication-result store. The input and parameter registers above, registers outside the workspace, and all tape payload are preserved; every register remains at most $M$. For the canonical irreducible modulus this computes multiplication in the binary extension field. The general modular-polynomial contract is reusable by both algorithms.''',
    'field_add': r'''Let $\ell\ge0$, $q=2^\ell$, and let $a,b<q$ encode binary coefficient vectors of length $\ell$. Let $s$ be a store with $R$ registers and $B$ buffers, $r$ an injective placement of a 27-register workspace, and $I$ any input. Suppose $M\ge1$, every register is at most $M$, and workspace registers $0,3,19,23$ contain $a,b,3\ell+1,q$.

The addition program reaches its specified result store with

$$t\le3000(M+1)^5,\qquad
s'[r(20)]=\operatorname{enc}(a\oplus b).$$

Here $\oplus$ is coefficientwise addition modulo two, including the empty-vector case $\ell=0$. The designated input and parameter registers, registers outside the workspace, and tape payload are preserved, and all registers remain at most $M$. When $\ell>0$, this is addition in the corresponding binary extension field.''',
    'field_inverse': r'''Let $\ell>0$, $q=2^\ell$, and let $a<q$ encode an element of the canonical binary extension field. Let $s$ be a store with $R$ registers and $B$ buffers, $r$ an injective placement of a 31-register workspace, and $I$ any input. Suppose $M\ge1$, every register is at most $M$, and the initial workspace satisfies the inversion setup conditions, including the canonical field parameters and encoded operand.

The inversion program reaches its specified result store with

$$t\le20000(M+1)^7,\qquad
s'[r(27)]=\operatorname{enc}(a^{-1}).$$

The operation is total, with $0^{-1}=0$. The designated input and parameter registers, registers outside the workspace, and tape payload are preserved, and every register remains at most $M$. This supplies the physical inverse operation used by Gaussian elimination.''',
    'sampler_layer': r'''Let $q=2^\ell$ with $\ell>0$, let $d$ be the point dimension, $k\le q$ the number of layers, $b>0$ the number of buckets, and $M\ge1$ a valid layer-capacity bound. Fix the encoded coefficient table of the two sampled linear forms per layer and fiber, the layer hash tables, a point $z\in\mathbb F_q^d$, and a layer index $i<k$.

For any input $I$ and store $s$ satisfying the sampler layer invariant, the layer program has an execution to $s'$ such that

$$t\le T_{\rm layer}(d,k,i,M),\qquad
s'[\operatorname{neighbor}(i)]=ib+h_i\bigl(\lambda_i(z),\mu_{i,\lambda_i(z)}(z),\nu_{i,\lambda_i(z)}(z)\bigr).$$

Here $T_{\rm layer}$ is the defined layer clock, $\lambda_i$ is the fixed first form, and the two other forms and $h_i$ are read from the supplied tables. The final store retains the layer invariant and the precise frame contract: the point, countdowns, other layers' neighbor registers, designated caller registers, output and tape payload are preserved. This isolates the actual execution of one sampler layer.''',
    'sampler_frontend': r'''Let $d\ge1$, $k>0$, and $n\ge\max\{2,k\}$. Let $r$ injectively place the sampler's 80-register workspace in a bank of $R$ registers. Give the machine the canonical unary encoding of $n$ and arbitrary remaining input tapes. Suppose $M$ satisfies the sampler-envelope conditions for $d,k,n$.

Starting from its specified initial store, the sampler frontend reaches exactly its specified initialization store and satisfies

$$t\le T_{\rm init}(d,n,M),\qquad
\mathcal R(s'),\qquad \operatorname{output}(s')=[\,].$$

The clock $T_{\rm init}$ is the defined frontend time. The readiness predicate $\mathcal R$ includes the size parameters, canonical field environment, random tables and register bounds needed by the row-writing phase. This separates initialization from the sampler's subsequent row and layer loops.''',
    'tester_frontend': r'''Let $d\ge4$, $n\ge2$, and let $y$ be a binary word of length $m=\operatorname{rowCount}(d,n)$. Supply the canonical encoding of $n$ followed by the bits of $y$, and suppose $M$ satisfies the tester-envelope conditions.

The tester frontend starts in its specified initial store and has an execution satisfying

$$t\le T_{\rm front}(d,n,M),\qquad \mathcal C(s'),
\qquad \operatorname{output}(s')=[\,].$$

Here $T_{\rm front}$ is the defined frontend clock. The core predicate $\mathcal C$ records the canonical field, auxiliary degree, word encoding and bounded workspace used by the Gram construction. The first two buffer heads equal one, and every buffer retains its bottom marker. This is the initialization interface for deterministic rank testing.''',
    'tester_gram': r'''Let $q=2^\ell$ with $\ell>0$, let $d$ be the point dimension, $D$ the monomial degree cutoff, $m=q^d$, and $y:\mathbb F_q^d\to\{0,1\}$ the received word. Let $s$ satisfy the tester core contract for these parameters, using $80+6d$ registers and three buffers. Assume its first buffer head equals one, the first two buffers have bottom markers, and

$$M\ge1,\qquad d(q-1)\le M,\qquad 1+mq\le M,\qquad m^2\le M.$$

For any input $I$, the Gram construction reaches the complete specified build state after

$$t\le T_{\rm Gram}(d,M,m).$$

The build state certifies all $m^2$ entries of the full padded Gram representation together with its storage and preservation invariants. The clock $T_{\rm Gram}$ is the defined program bound. This isolates construction of the matrix from its later rank computation.''',
    'gaussian_rank': r'''Fix a point dimension $d$, an input size $n$, and a binary word $y$ of length $m=\operatorname{rowCount}(d,n)$. Let $s$ be a Gaussian-program store satisfying the common field, size and workspace invariant with bound $M$. Assume buffer zero contains the canonical encoded binary test table for $y$ and buffer one contains an arbitrary $m\times m$ workspace table. Let $I$ be any input.

The finite rank program has an execution to $s'$ satisfying

$$t\le100000(M+1)^9,\qquad
s'[48]=\operatorname{rank}_{\mathbb F_q}\!\left(V\operatorname{diag}(y)V^{\mathsf T}\right).$$

Here $q$ is the specified field size and $V$ is the canonical auxiliary-monomial evaluation matrix. The common invariant is preserved, register 62 is zero, and the read heads and output are unchanged. This certifies the physical Gaussian-elimination stage used by the rank test.''',
}


def main():
    nodes = json.loads((BASE / 'partition/nodes.json').read_text())
    frozen = json.loads((BASE.parent / 'runs/final-source-manifest.json').read_text())['files']
    problems = []
    for node in nodes:
        path = node['original_module'].replace('.', '/') + '.lean'
        problem = {
            'theorem_name': node['theorem_name'], 'theorem_title': node['title'],
            'preamble': node['preamble'], 'formal_statement': node['formal_statement'],
            'natural_language_statement': TEXT[node['key']],
            'source': (node['source'] + ' Supporting formal implementation contract, rather than '
                'a verbatim statement in the paper. Exact local source: ' + path + ', declaration '
                + node['theorem_name'] + '; source file SHA256 ' + frozen[path] + '. '
                'The public construction is at https://prove2.me/missions/Expanding_Codes_with_Polynomial_Stretch.'),
            'tags': [TAG, 'complexity-theory', 'coding-theory']}
        problems.append(problem)
    payload = {'problems': problems, 'env': ENV, 'private': False}
    destination = BASE / 'partition-problems-payload.json'
    destination.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps({'problems': len(problems), 'path': str(destination),
        'sha256': hashlib.sha256(destination.read_bytes()).hexdigest()}))


if __name__ == '__main__':
    main()
