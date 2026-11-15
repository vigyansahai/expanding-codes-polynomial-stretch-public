#!/usr/bin/env python3
"""Write mathematical proof explanations for the ten runtime helper submissions."""
import json
from pathlib import Path

BASE = Path(__file__).resolve().parent
EXPLANATIONS = {
    'tape_compile': r'''The compilation theorem concerns an arbitrary finite source program, independently of the expanding-code algorithms. Source registers are represented by unary work tapes; source buffer operations are represented by individual tape reads, writes and head moves. A representation relation identifies the source configuration with the compiled machine configuration, including all heads and the complete output.

Each instruction has a verified finite simulation. The initial machine step establishes the representation relation, and every source instruction costs at most two machine transitions. Induction over the source execution therefore gives the bound $1+2t$. If the source configuration is halted after $t$ instructions, the corresponding compiled configuration is halted and has the same output under the canonical bit-to-symbol encoding. The argument holds for every oracle and input. All instruction cases are proved in the submitted source; the theorem assumes only the stated source halting condition.''',
    'field_setup': r'''Put $q=2^\ell$. The program searches the finite encodings of monic degree-$\ell$ binary polynomials and tests the bounded factor certificates used by the canonical modulus definition. The defining algebraic lemmas provide an irreducible candidate; the search invariants identify the selected candidate with the canonical least index. The search is executed by the physical source program, rather than supplied as a field oracle.

The setup execution theorem composes coefficient-bound preparation, modulus search and the final register assignments. Its invariant tracks both the polynomial specification and the caller's register bound. The hypotheses $3\ell+1\le M$, $2q\le M$ and $q^2\le M$ cover the coefficient and search ranges. The proved loop clocks combine to at most $40000(M+1)^7$. The final-state equalities establish the field environment, preserve every register outside the injective workspace, and preserve the read heads, output, buffer contents and buffer heads.''',
    'field_multiply': r'''The operands encode binary polynomials of degree below $\ell$, and the supplied modulus is monic of degree $\ell$. Polynomial division by this monic polynomial supplies a remainder of degree below $\ell$ and a bounded quotient. Conversely, the finite coefficient certificate checked by the program implies the same polynomial identity, so its remainder is unique. Irreducibility is unnecessary for this modular-product theorem.

The source execution computes and checks those certificates using finite coefficient and convolution loops. Their invariants identify the physical register result with the canonical remainder index. The initial parameter registers and the common bound $M$ bound all search ranges and intermediate counters; the composed execution clock is at most $10000(M+1)^6$. The frame lemmas prove the entire specified result store and all caller-state preservation clauses. Thus the theorem certifies the actual finite program, including its runtime, and specializes to field multiplication for the canonical irreducible modulus.''',
    'field_add': r'''Binary coefficient-vector addition is characterized by the coefficientwise parity equations. The finite sum encoding is unique, including the length-zero case. The program's bounded coefficient operations are proved to satisfy exactly these equations, which identify its output register with the canonical addition index.

The execution proof composes the finite coefficient loops and propagates their register and tape invariants. The stored values of $\ell$, $q$ and the operands, together with the initial bound $M$, control the counters and give the clock $3000(M+1)^5$. The final-store equality and frame facts establish every preservation clause. For positive extension degree this is the required field addition, while the proof retains its stated generality for arbitrary nonnegative coefficient length.''',
    'field_inverse': r'''The canonical irreducible modulus makes the encoded quotient a field. For a nonzero operand, a multiplicative inverse exists among the $q=2^\ell$ encodings. The finite inverse certificate characterizes the successful candidates and identifies the selected result with the canonical inverse index. The zero operand is handled separately, with the specified total value zero.

The program performs the bounded search and certificate checks on its actual work tapes. The setup predicate supplies the field parameters and initial register configuration needed by those executions. Their loop invariants yield the specified inverse-result store, the register bound and the complete preservation frame. Combining the proved clocks gives $20000(M+1)^7$; no inverse oracle is assumed.''',
    'sampler_layer': r'''Fix a point, a layer, and the encoded coefficient and hash tables. The layer program first evaluates the fixed linear form of the point. It then reads the two linear forms assigned to that fiber, evaluates them, and looks up the corresponding hash entry. The verified source addition and modular-multiplication routines implement the field operations used by these evaluations.

The evaluation and lookup invariants identify the final neighbor register with the layer offset plus the canonical hashed triple. The injective storage layout and the primitive frame lemmas preserve the point, countdowns, designated caller registers, output and tape payload; every other layer's neighbor register is unchanged. The capacity hypotheses bound the inner loops and field parameters, and their composed clocks give the defined layer-time bound. This proves one actual layer execution, which the sampler's outer loops can reuse.''',
    'sampler_frontend': r'''The frontend is a composition of size-parameter setup, random-table construction and canonical field setup. Starting from the specified initial store and unary size input, the first phase establishes the size and bucket parameters. The table phase reads the required coefficient and hash data from the random tape into its specified storage representation. The field phase establishes the canonical modulus and arithmetic environment.

Each phase has a proved source execution and a frame specifying the state it preserves. The sampler-envelope conditions supply the bounds required by these component contracts. Composing their executions gives the specified initialization store, the complete runtime-ready invariant and empty output. The sum of the component clocks is the defined frontend time. The theorem concerns the actual initialization program; the later layer and row loops are separate obligations.''',
    'tester_frontend': r'''The input consists of the canonical size encoding followed by the received word. The frontend reads this input, computes the size and degree parameters, constructs the canonical binary-field environment, and establishes the storage layout used by the Gram program. The field-setup theorem is applied with the register bounds furnished by the tester envelope.

The execution invariants identify the decoded word with the supplied binary word and the stored degree with the canonical auxiliary cutoff. The frame facts preserve empty output, establish the first two buffer-head positions and retain all bottom markers. Composing the phase executions gives the tester core predicate and the defined frontend clock. This establishes initialization without assuming the later matrix construction or elimination routines.''',
    'tester_gram': r'''The construction enumerates the bounded exponent grid and field points. Its nested loops evaluate monomials, combine the received-word bit with the two monomial values, and accumulate the field sum for each Gram entry. Entries excluded by the degree cutoff are represented by the prescribed zero padding. The source field-addition and multiplication contracts justify these arithmetic steps.

Loop induction maintains the partial matrix-build invariant and its storage frame. After all $m^2$ positions have been processed, that invariant is exactly the complete build-state predicate in the conclusion. The bounds on $d(q-1)$, $1+mq$ and $m^2$ supply the register, input-buffer and matrix capacities used by the component executions. Their clocks compose to the defined Gram-program time. The proof constructs the actual finite execution and certifies the stored matrix, ready for the separate rank program.''',
    'gaussian_rank': r'''The elimination program maintains a representation of the active matrix together with its accumulated pivot count. Pivot search distinguishes an available nonzero pivot from an empty search. In the pivot case, the verified field-inversion, multiplication and addition routines implement the row operations; their algebraic specifications show how the residual rank and pivot count change. The empty-search case accounts for a zero remaining rank.

The driver invariant carries these facts through the finite elimination grid. Its conclusion identifies the count with the rank of the stored full test table. The padding and evaluation lemmas identify that rank with the canonical auxiliary-monomial test-matrix rank. Physical storage, marker and caller-frame invariants compose throughout the execution. The proved driver clock is at most $100000(M+1)^9$, and its final state has the required zero control register, preserved read heads and output, and restored common invariant.''',
}


def main():
    nodes = json.loads((BASE / 'partition/nodes.json').read_text())
    directory = BASE / 'explanations'
    directory.mkdir(exist_ok=True)
    for node in nodes:
        (directory / (node['key'] + '.txt')).write_text(EXPLANATIONS[node['key']] + '\n')
    print('Wrote explanations for ' + str(len(nodes)) + ' runtime helper proofs.')


if __name__ == '__main__':
    main()
