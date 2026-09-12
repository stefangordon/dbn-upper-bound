# Lean 4 formalization

The headline theorem remains conditional:

~~~lean
DBN.lambda_le_bound_of_remaining :
  DBN.RemainingPremises → DBN.Lambda ≤ (DBN.Const.bound : ℝ)
~~~

The exact bound is
`3885632262767861213460393068710302759 / 24646172707879668706230182733520000000`.
Lean has **not** proved this bound without analytic inputs.

## The three interfaces

| Interface | Explicit inputs |
|---|---|
| `lambda_le_bound_of_remaining` | Positive-time confinement, the full finite head, source floors, field floors |
| `lambda_le_bound_of_polymath_and_profiles` | The named Polymath tail proposition; finite head, source floors, analytic density/jet comparisons |
| `lambda_le_bound_of_approximation` | Enlarged approximation, finite RH at time zero, continuous boundary main-term lower bound, source floors, analytic density/jet comparisons |

The original four-field `RemainingPremises` structure is preserved. Its
`head` field still states the whole finite-head conclusion, rather than a
stronger replacement hypothesis. The second interface retains that head input
and removes the formerly assumed P8 gates because they are now proved.
The third interface derives the head and confinement from more explicit inputs.

[Audit.lean](Audit.lean) checks the original premise constructor as well as
the headline theorem types and literal rational constant. Merely retaining a
theorem name while strengthening its hypotheses would not pass this audit.

## Reproduce

From this directory:

~~~sh
python3 scripts/gen_data.py --check
lake exe cache get
lake build
lake env lean Audit.lean
~~~

Lean `leanprover/lean4:v4.33.1`, mathlib `v4.33.1`, and leancert revision
`4ea18bb66dfcd7f18f260bc25302400f5a3cafd7` are pinned.
Use at least 32 GiB RAM. The rational barrier certificate took about 13 minutes
and reached roughly 15 GiB during preparation. The full P8 reduction is another
substantial computation; budget approximately 40 minutes. Cached builds are not
fresh re-evaluations of those certificates.

The generator reads only [barriers.json](../certificate/data/barriers.json).
Its `--check` compares all 30 generated files byte for byte, without writing.
Normalization of the earlier certificate preserved every mathematical
declaration; only provenance headers changed.

## What is kernel-checked

- All rational row gates, joins, wall and catalog conditions, and endpoints
  for the 4,817 main and 7,849 reference rows.
- Barrier calculus, force/kernel inequalities and the first-contact argument.
- Simple-zero branches, backward splitting at multiple zeros and paired
  zero-sum force laws, assembled as `DBN.zeroDynamics_proved`.
- The concrete-integral bridge to pinned leancert, supplying strip contraction,
  initial strip, symmetry, continuity, the xi identity, and boundedness below
  of real-zero times.
- The explicit profile formulas, positivity and time monotonicity of `U`
  and `f0 = UY/U`, the subtraction budget and whole-cell transfer.
- Every P8 endpoint inequality, including all reused main-row certificates.
- Finite-head propagation from a time-zero real-zero input and vertical
  boundary nonvanishing.
- The boundary error threshold and required positive-time confinement,
  conditional on the enlarged approximation and the other inputs shown above.
- Auxiliary zeta, finite heat-sum and remainder identities described below.

### Complete P8 certificate

[GateChecker.lean](DBN/GateChecker.lean) implements a rational fixed-point
evaluator for `exp`, `cosh` and `sinh`: 20 Taylor terms on `x/64`, six
squarings, and directional rounding to multiples of `2⁻¹⁰⁰`. Its enclosure
and gate-soundness proofs use Mathlib's real exponential estimates.

Kernel reduction checks every field certificate in both frozen barriers:
12,125 density occurrences and 9,089 signed jet occurrences. These include
the reused main certificates; the unique reference gates number 7,849 and
6,317 respectively. Source rows do not require P8 and are excluded by their
certificate constructor, not by an unchecked selection flag.

The final theorem is `DBN.Profile.profileCellGates_proved`. It proves exactly
`s + 1/100000 < f0 p tl` and, for signed rows, `Cceil p tl tr ≤ c`.
There is no native-evaluation fallback. It does **not** prove the analytic
density/jet comparisons or nonvanishing of the actual heat flow.
[FieldTransfer.lean](DBN/FieldTransfer.lean) remains a compositional lemma
with an explicit P8 parameter; `GateChecker` now supplies that parameter.

[ProfileChecks.lean](DBN/ProfileChecks.lean) retains independent kernel checks
through leancert's interval evaluator: density rows 1251 and 3356, jet rows
3356 and 5845, and the refutation of the earlier extra-subtraction condition
at row 3356. The smallest observed density and jet margins are about
`4e-12`. This separate module took about 17 seconds and 9.6 GiB.

### Finite head

[Head.lean](DBN/Head.lean) proves `DBN.head_of_finiteRH`:

~~~lean
FiniteRH → BoundaryNonvanishing →
  ∀ t ∈ Set.Icc (0 : ℝ) (1 / 5), ∀ z : ℂ,
    H t z = 0 → |z.re| ≤ Const.X → z.im = 0
~~~

`FiniteRH` is the time-zero statement in the `H)-coordinate.
Since `H₀(z) = ξ((1+iz)/2)/8`, its corresponding zeta ordinate cutoff is
`X/2 = 2999673670750`, not `X`. The cited Platt–Trudgian theorem and its
identification with this formal proposition are still external inputs.

The proof uses [ZeroCount.lean](DBN/ZeroCount.lean), an argument principle
derived from the existing Hadamard logarithmic-derivative formula;
[HermiteRoots.lean](DBN/HermiteRoots.lean), giving the distinct real roots
of the model polynomial; and [HermiteForward.lean](DBN/HermiteForward.lean),
giving forward-time splitting. Local zero counts and conjugation imply
reality; continuous induction covers the entire closed time interval.

### Approximation and confinement

[Approximation.lean](DBN/Approximation.lean) defines the manuscript's functions
and collects the residual estimate and nonzero normalizer into
`EnlargedApproximation`. **This proposition is an assumption, not a proved
approximation theorem.** It covers `x ≥ 5.9·10¹²`, `t ∈ [0,1/5]`,
`y ∈ [0,7]`.

`BoundaryMainTermBound` assumes `|f^{[N]}(X+iy)| > 1/500` at every point
of the continuous time-height rectangle. It is **not a Lean-checked grid**.
The conventional argument derives it from the 800,000-cell polynomial check
(C8) and the Taylor error (C7); formalizing that bridge and computation
remains open. Lean proves that this assumption and `EnlargedApproximation`
imply boundary nonvanishing, using a proved scalar error bound below `1/500`.

[GammaEstimate.lean](DBN/GammaEstimate.lean) proves the coarse bound
`|γ| ≤ exp(1/10) Q^(−y/2)` on `x ≥ X_e`, `t ∈ [0,1/5]`, `y ∈ [0,1]`.
This is not the sharper full-domain estimate from the paper.

[ConfineApprox.lean](DBN/ConfineApprox.lean) derives the exact confinement
needed here, for zeros with `|Im z| ≥ 1/40` on a compact positive-time
interval, from `EnlargedApproximation`. Its radius is
`max X_e (4π exp(80/t₀))`. The finite heated sums are controlled only for
`2 ≤ n ≤ N(x,t)`; no infinite positive-time heated series is invoked.
This does not formalize the full Polymath real-zero tail theorem.

The alternative [Confinement.lean](DBN/Confinement.lean) keeps that published
tail proposition explicit and proves its required corollary.

### Auxiliary source lemmas

These are useful components, not a formal proof of the 26 source floors:

- [ZetaBounds.lean](DBN/ZetaBounds.lean): the Euler-product modulus lower
  bound and the **termwise** common-phase inequality underlying (C25).
- [VonMangoldtSeries.lean](DBN/VonMangoldtSeries.lean): the absolutely
  convergent Dirichlet series for `Φ_t = −ζ'/ζ − (t/4)(ζ''/ζ)'` on
  `Re s > 1`. Its coefficients are nonnegative for `t ≥ 0`, and the
  value modulus bound is proved. The derivative bound is not yet proved.
- [HeatIdentity.lean](DBN/HeatIdentity.lean): the exact finite decomposition
  (C13) for all real `t`, all natural cutoffs and `Re s > 1`, together
  with a finite-remainder norm bound and an infinite-tail norm bound.
  The latter requires `t ≥ 0`. The stronger uniform majorants (C14–C16),
  derivative estimates, Cauchy reductions and final numerical gates remain open.

## Remaining trust boundary

The approximation-based headline still assumes `EnlargedApproximation`,
`FiniteRH`, `BoundaryMainTermBound`, the source floors and the analytic
density/jet comparisons. None is inserted as a project axiom.

The audit checks 27 principal declarations and permits only `propext`,
`Classical.choice` and `Quot.sound`. These foundational axioms are
disclosed; their being the only axioms does not discharge explicit theorem
hypotheses. See [verification scope](../VERIFICATION.md) for the conventional
evidence supporting those hypotheses.
