import hashlib
import json
from pathlib import Path

context = [
    'AGENTS.md',
    'Definitions/Def_ExpandingCodes_PolynomialStretch_PolynomialTest.lean',
    'Definitions/Def_ExpandingCodes_PolynomialStretch_ErasureModel.lean',
    'ExpandingCodes/Probability/HalfspaceVolume.lean',
    'ExpandingCodes/Probability/GridVolume.lean',
    'ExpandingCodes/Probability/RateLimit.lean',
    'ExpandingCodes/Algebra/ReedMullerDimension.lean',
    'ExpandingCodes/Construction/Growth.lean',
]
sources = [
    {'path': 'tmp/feasibility/paper.txt', 'lines': '555-575', 'role': 'Paper Lemma 2.4 identifies the normalized reduced-monomial count with the continuous-uniform cube-halfspace mass.'},
    {'path': 'Definitions/Def_ExpandingCodes_PolynomialStretch_PolynomialTest.lean', 'lines': '8-18', 'role': 'Unchanged exact canonical Monomials, reedMuller and auxiliaryDegree definitions.'},
    {'path': 'Definitions/Def_ExpandingCodes_PolynomialStretch_ErasureModel.lean', 'lines': '35-40', 'role': 'Unchanged limitingRate as actual ambient Lebesgue volume, and exact auxiliaryCode.'},
    {'path': '.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean', 'lines': '195-207', 'declaration': 'MeasureTheory.Measure.addHaar_affineSubspace', 'role': 'A proper coordinate-sum affine hyperplane is Lebesgue null.'},
    {'path': '.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Indicator.lean', 'lines': '45-61', 'declaration': 'MeasureTheory.tendsto_measure_of_ae_tendsto_indicator', 'role': 'Continuous moving-halfspace volume from eventual pointwise membership outside the null hyperplane, dominated by the unit cube.'},
    {'path': '.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean', 'lines': '268-275', 'declaration': 'Real.volume_pi_Ico', 'role': 'Every half-open mesh box has exact product volume q^(-d).'},
    {'path': '.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean', 'lines': '505-511', 'declaration': 'MeasureTheory.Measure.univ_pi_Ico_ae_eq_Icc', 'role': 'Removing the upper faces from the canonical closed cube does not alter volume.'},
    {'path': 'ExpandingCodes/Algebra/ReedMullerDimension.lean', 'declaration': 'ExpandingCodes.PolynomialStretch.finrank_reedMuller', 'role': 'Checked independent algebraic dimension equality; used only after the pure natural-count limit is proved.'},
]
route = ('Use exact integer division inequalities to bound auxiliaryDegree(q,d)/q between (d-3)/2-d/q and (d-3)/2. '
         'Prove the coordinate-sum level set is a proper affine subspace and hence Lebesgue null. Dominated indicator convergence yields continuity of the actual cube-halfspace volume in its threshold. '
         'Partition the half-open unit cube into pairwise disjoint boxes [a_i/q,(a_i+1)/q). Their selected union has exact Lebesgue volume card(GridIndices)/q^d. '
         'Coordinatewise floors give the lower inclusion of the halfspace at R/q, after null upper faces are removed; summing box upper bounds gives the upper inclusion in the halfspace at (R+d)/q. '
         'Both thresholds converge to the same target, so real-valued volume squeeze proves the moving-degree natural-count limit. '
         'Finally apply the independently proved exact finite Reed--Muller dimension equality and fieldSize growth, preserving arbitrary mission Geometry choices and the exact rowCount denominator.')
statements = [
    ('auxiliary_monomial_rate_limit', 'ExpandingCodes.PolynomialStretch.tendsto_auxiliary_monomialCount_div',
     '∀ (d : ℕ), 4 ≤ d → Filter.Tendsto (fun q : ℕ => (Fintype.card {a : Fin d → Fin q // ∑ i, (a i).val ≤ ExpandingCodes.PolynomialStretch.auxiliaryDegree q d} : ℝ) / (q : ℝ) ^ d) Filter.atTop (nhds (ExpandingCodes.PolynomialStretch.limitingRate d))'),
    ('auxiliary_rate_limit', 'ExpandingCodes.PolynomialStretch.tendsto_auxiliaryCode_rate',
     '∀ (d : ℕ), 4 ≤ d → ∀ (g : ∀ n : ℕ, ExpandingCodes.PolynomialStretch.Geometry d n), Filter.Tendsto (fun n : ℕ => (Module.finrank (g n).F (ExpandingCodes.PolynomialStretch.auxiliaryCode (g n)) : ℝ) / ExpandingCodes.PolynomialStretch.rowCount d n) Filter.atTop (nhds (ExpandingCodes.PolynomialStretch.limitingRate d))'),
]
nodes = []
for node_id, declaration, statement in statements:
    nodes.append({
        'id': node_id,
        'declaration': declaration,
        'file': 'ExpandingCodes/Probability/RateLimit.lean',
        'statement': statement,
        'statement_sha256': hashlib.sha256(statement.encode()).hexdigest(),
        'proof_route': route,
        'owner': 'rate_limit',
        'status': 'open',
        'interface': 'provisional',
        'dependencies': [],
        'context_files': context,
        'sources': sources,
        'failed_attempts': [
            {'approach': 'Use the library lattice-point Riemann-sum theorem tendsto_card_div_pow_atTop_volume.', 'result': 'A viable alternate route was found in Mathlib.Analysis.BoxIntegral.UnitPartition. It requires a separate lattice-subtype/finite-exponent equivalence and a moving-threshold extension. Replaced before proof work by the direct finite box partition, whose floor inclusions give the moving-threshold result directly.'},
            {'approach': 'Treat half-open/closed cube a.e. equality as a membership iff without coercions.', 'result': 'Lean ae equality is equality of predicates. Resolved by explicit set type annotation, propext, and Iff.of_eq. No mathematical obstruction.'},
        ],
        'review': {
            'reviewer': 'rate_limit self-review; independent coordinator review pending',
            'statement_preserved': True,
            'strictly_useful': True,
            'notes': 'Local helper interfaces are provisional, while every platform definition and the exact Lebesgue target remain unchanged. No altered distribution, fixed alphabet, fixed Geometry, hypothesis weakening, custom axiom or proof hole. Administrative open status reserves harness receipt and independent coordinator review; worker verification results are recorded separately.',
        },
    })
record = {
    'schema_version': 1,
    'versions': {'lean': 'leanprover/lean4:v4.33.1', 'mathlib': '0df444a360eaa60ab8c11dca51a86af692955474'},
    'allowed_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
    'owner': 'rate_limit',
    'file_ownership': ['ExpandingCodes/Probability/RateLimit.lean', 'ExpandingCodes/Probability/GridVolume.lean', 'ExpandingCodes/Probability/HalfspaceVolume.lean', 'harness/attempts/rate_limit/', 'harness/tasks/rate_limit.json'],
    'nodes': nodes,
    'worker_result': {
        'status': 'final_draft_pending_check',
        'open_theorem_bodies': [],
        'unresolved_dependencies': [],
        'scope': 'Exact limiting-rate convergence only; the lower/upper numerical limitingRate bounds and erasure-expectation decay remain independent branches.',
        'supporting_declarations': [
            'auxiliaryDegree_scaled_bounds', 'tendsto_auxiliaryDegree_div', 'volume_coordinateSum_eq_zero',
            'tendsto_volume_cubeHalfspace', 'continuous_cubeHalfspace_volume', 'pairwiseDisjoint_gridBox',
            'volume_truncatedGrid', 'truncatedGrid_subset_cubeHalfspace',
            'cubeHalfspace_inter_halfOpenCube_subset_truncatedGrid', 'cubeHalfspace_inter_halfOpenCube_ae',
            'tendsto_gridCount_div', 'tendsto_reedMuller_rate', 'tendsto_fieldSize_atTop',
        ],
        'compiler_policy': 'Only short-lived serialized tools/lake-serial compiler jobs at the coordinator-approved 6144 MB default and one thread. No persistent REPL. Worker never changes memory cap.',
        'checked_commands': [
            {'command': './tools/lake-serial env lean -DautoImplicit=false harness/attempts/rate_limit/RateLimit.lean', 'exit_code': 0, 'scope': 'Canonical initial HalfspaceVolume draft before promotion.'},
            {'command': './tools/lake-serial build ExpandingCodes.Probability.HalfspaceVolume', 'exit_code': 0},
            {'command': './tools/lake-serial env lean -DautoImplicit=false harness/attempts/rate_limit/GridVolume.lean', 'exit_code': 0, 'scope': 'Canonical GridVolume draft before promotion.'},
            {'command': './tools/lake-serial build ExpandingCodes.Probability.GridVolume', 'exit_code': 0},
        ],
    },
}
Path('harness/tasks/rate_limit.json').write_text(json.dumps(record, indent=2) + '\n')
