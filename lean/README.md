# Lean 4 formalization

The headline theorem is conditional:

```lean
DBN.lambda_le_bound_of_remaining :
  DBN.RemainingPremises → DBN.Lambda ≤ (DBN.Const.bound : ℝ)
```

The bound is the exact rational
`3885632262767861213460393068710302759 / 24646172707879668706230182733520000000`.
Lean has **not** proved the conclusion without analytic premises.

An additional theorem, `DBN.lambda_le_bound_of_polymath_and_profiles`, exposes a more detailed
boundary. It takes the explicitly named Polymath real-zero tail proposition and
`ProfileRemainingPremises`: the finite head (P2), source floors (P7), analytic
density/jet field comparisons (P4/P5), and all numerical endpoint gates (P8).
Lean proves that these imply every field of the original `RemainingPremises`.

## Reproduce

From this directory:

```bash
python3 scripts/gen_data.py --check
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean is pinned to `leanprover/lean4:v4.33.1`; mathlib to `v4.33.1`; leancert to
commit `4ea18bb66dfcd7f18f260bc25302400f5a3cafd7` in the lockfile.
The first build compiles leancert's analysis and interval libraries from source.
The full rational certificate is deliberately checked by kernel reduction and
takes minutes: 754 seconds (12.6 minutes) on the preparation machine for this
publication update. It is not a seconds-long smoke test.

The generator reads only [barriers.json](../certificate/data/barriers.json).
`--check` writes nothing and compares all 30 generated files byte for byte.
During preparation, a separate migration comparison established that data
normalization preserved every declaration byte before the provenance headers
were updated. The published checker compares the complete files.

## What is proved

The main theorem uses the following kernel-checked components:

- The exact rational row gates, chain joins, endpoints, wall and source-catalog
  checks for the 4,817 main rows and 7,849 reference rows.
- Piecewise affine barrier calculus, the force inequalities and kernel
  minorants, and the first-contact comparison, including strict entry of the
  main barrier from the reference barrier at the cushion time.
- The differentiable branch through a simple zero, backward Hermite splitting
  at a multiple zero, and the pair-sum force laws. Together these prove
  `DBN.zeroDynamics_proved`.
- The lower bound for `Omega`.
- Through the proved definition bridge to pinned
  [leancert](https://github.com/alerad/leancert/tree/4ea18bb66dfcd7f18f260bc25302400f5a3cafd7/LeanCert/Analysis/DBN):
  de Bruijn strip contraction, boundedness below of real-zero times, the
  initial strip, symmetry, joint continuity, and the xi-function identity.
- The explicit profile formulas, positivity and time monotonicity of `U`,
  time monotonicity of `f0 = UY/U` at nonnegative height, the uniform subtraction
  budget, and the whole-cell jet ceiling.
- The rational wall geometry and the precise transfer from P4/P5 and the P8
  endpoint gates to the complete `fieldFloor` premise, for every old cell used.

The P8 density gate is exactly `s + 1/100000 < f0 p tl`. Combining it with
`delta t < 1/100000` and P4, `S ≥ f0 - delta`, gives `S > s`.
No monotonicity of `fM = f0 - delta` is required.

## Bounded P8 kernel checks

[ProfileChecks.lean](DBN/ProfileChecks.lean) proves four numerical inequalities:

| Gate | Zero-based reference row |
| --- | ---: |
| Density, smallest margin found by the conventional interval audit | 1251 |
| Density | 3356 |
| Jet | 3356 |
| Jet, smallest margin found by the conventional interval audit | 5845 |

Their exact inputs are linked to the frozen row data by kernel-checked tuple
equalities. Both smallest margins are approximately `4e-12`.
The file also proves `overderated_3356_false`: the formerly printed stronger
condition `s < fM p tl - 1/100000` is false at row 3356. The accepted checker
gate and final bound are unchanged.

All five numerical statements use leancert with `trust := kernel`; there is
no native fallback. Rechecking this module took about 17 seconds and peaked at
9.6 GiB on the preparation machine. These checks cover only the listed gates,
not all P8 rows. The complete P8 numerical verification is supplied by the
separate Arb and mpmath certificate checkers.

## What remains assumed

`RemainingPremises` still contains positive-time confinement, the finite head,
the source floors, and the field floors. The more explicit interface separates
the last item into analytic P4/P5 and the full P8 endpoint list.

[Confinement.lean](DBN/Confinement.lean) names
`PolymathPositiveTimeRealTail`: there exists `C > 0` such that, for
`0 < t ≤ 1/2`, every zero with `Re z ≥ exp(C/t)` is real. This is the
real-zero conclusion of [Polymath, arXiv:1904.12438v2, Theorem 1.5(i)](https://arxiv.org/html/1904.12438v2).
Lean proves the exact compact-time confinement consequence with
`R = exp(C/t0)`, using the proved evenness for negative real parts.
The literature theorem itself remains an explicit premise; it was not inserted
as an axiom or represented as an already formalized proof.

See the publication's [verification scope](../VERIFICATION.md) for the conventional
analytic evidence and the unresolved formalization work.

## Audit and layout

[Audit.lean](Audit.lean) checks the exact headline types, prints the premise
structures and transitive axiom dependencies, and uses `#assert_trust kernel`
to reject proof holes, compiler/native dependencies, or unrecognized axioms in
the audited declarations. The permitted foundations are `propext`,
`Classical.choice`, and `Quot.sound`. This is not an axiom-free development.

| Files | Role |
| --- | --- |
| `Constants`, `Certificate`, `Data/*`, `Check` | Exact constants, data, gates and finite proofs |
| `Barrier`, `Algebra`, `Kernels`, `FirstContact` | Barrier comparison and force inequalities |
| `Heat`, `Identification`, `External`, `OmegaGap` | Concrete analytic objects and established formal components |
| `ZeroBranch`, `Hermite`, `PairSum` | Zero dynamics |
| `Confinement` | Precisely stated literature parameter and proved corollary |
| `Profile`, `WallGeometry`, `FieldTransfer` | Profile calculus, geometry and exact P4/P5/P8 transfer |
| `ProfileChecks` | Four difficult P8 gates and the misprinted-gate counterexample |
| `Premises`, `Main` | Remaining hypotheses and conditional bound |
