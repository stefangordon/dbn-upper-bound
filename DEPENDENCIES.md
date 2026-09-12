# Proof dependencies

All functions and domains are defined in the [main paper](manuscript/main.md).
These are mathematical inputs, not acceptance flags.

| Input | Scope | Proof or source | Executable evidence |
|---|---|---|---|
| Classical heat flow and zero dynamics | Concrete integral, regularized zero sums, branch velocity and backward splitting | Polymath [Po19], Section 3; `DBN.External`, `ZeroBranch`, `Hermite`, `PairSum` | Lean kernel |
| Strip contraction | Strip half-width \(h\) at \(t\) gives real zeros at \(t+h^2/2\) | de Bruijn; Polymath Theorem 3.2; `DBN.External` | Lean kernel |
| P3a: confinement | One real-part bound on a compact positive-time interval | Polymath Theorem 1.5(i); \(R=e^{C/\tau}\); or Lean's `DBN.confine_of_approximation` from P3b | Lean proves the corollary from an explicit literature parameter, and derives the required fixed-height confinement from `DBN.EnlargedApproximation` |
| P3b: approximation | \(x\ge5.9\cdot10^{12}\), \(0\le t\le1/5\), \(0\le y\le7\) | Appendix A.1–A.3; generic-real-part Arias de Reyna expansion; collected as the unproved proposition `DBN.EnlargedApproximation` | `support/fields/check_h7.py` |
| P2a: finite RH at \(t=0\) | Every zero of \(H_0\) with \(|\Re z|\le5999347341500\) is real | Platt–Trudgian Theorem 1 (\(X/2<3\cdot10^{12}\)); premise `DBN.FiniteRH` | Cited theorem; not recomputed |
| P2b: boundary non-vanishing | \(H_t(X+iy)\ne0\), \(0\le t\le1/5\), \(0\le y\le1\) | Appendix C.2; premise `DBN.BoundaryNonvanishing`; Lean derives it from P3b and the continuous lower-bound assumption `DBN.BoundaryMainTermBound` (`boundaryNonvanishing_of_approximation`, with (C4) proved) | `support/head/` matrix regeneration, full grid, direct sums |
| P2c: head propagation | P2a and P2b give: every zero with \(|\Re z|\le X\) is real, \(0\le t\le1/5\) | Appendix C homotopy; `DBN.ZeroCount`, `HermiteRoots`, `HermiteForward`, `Head` | Lean kernel (`DBN.head_of_finiteRH`) |
| P4: density | \(S\ge U_Y/U-e^{90t}/10^{14}\), \(x\ge X\), \(\sqrt{q_M(t)}<Y\le5\) | Appendix A, coupled density/wall comparison | `check_m3a.py`: 855 initial leaves, 1620 bottom cells and wall rows |
| P5: jet | \(J\le C\), \(x\ge X\), \(\sqrt{q_M(t)}+3/5\le Y\le5\) | Appendix A, differential inequality and boundary proof | `check_fixed_c.py`, `check_early_boundary.py`, `check_late_boundary.py` |
| P7: source | \(V>L\), all \(x\ge X\), on each closed source box | Appendix C.3; P3b and elementary Dirichlet-series bounds; no wall or jet input; auxiliary Lean results cover the Euler-product lower bound, the termwise inequality underlying (C25), the Dirichlet series for `Φ_t`, and the finite heat identity (C13), but not the full source-floor theorem | `support/source/verify.py`: all 26 boxes and 78 probes |
| P8: profile values | \(s+10^{-5}<U_Y/U\); signed jet ceiling at each reference cell | Main Section 4; `DBN.Profile`, `FieldTransfer`, `GateChecker` | Lean kernel for every gate (`DBN.Profile.profileCellGates_proved`); also all rows with two arithmetic libraries |
| Barrier comparison | 4817 main rows, 7849 reference rows; terminal height \(1/400\) | Main Sections 5–7; `DBN.Certificate`, `FirstContact`, `Main` | Exact Python checks and Lean kernel |

P4 and P5 hold throughout \(0\le t\le T_M\). Their full quantifiers are printed
in the paper and formal premise structure.

The useful order is: P3b supplies the finite-head and source estimates; P3b and
the finite head supply the coupled density/wall comparison; these supply the
jet comparison; the profile gates and source floors supply the final barrier
comparison. The source floors are independent of the density and jet fields.
The conventional first-contact proof uses the published confinement theorem; the alternative Lean interface derives the required confinement from the enlarged approximation.

The exact support-data identities are checked by `certificate/check_support.py`.
The JSON-to-Lean translation is checked by `lean/scripts/gen_data.py --check`.
No prior proposed bound or campaign acceptance decision is an input.

## Formal boundary

The original interface is
`RemainingPremises → Lambda ≤ bound`.
The additional interface is
`PolymathPositiveTimeRealTail → ProfileRemainingPremises → Lambda ≤ bound`.
It retains the full P2 head input and separates P7 and the analytic P4/P5
comparisons; the now-proved P8 gates are no longer an input. The original
four-field `RemainingPremises` interface is preserved. The third interface is
`ApproximationPremises → Lambda ≤ bound` (`DBN.lambda_le_bound_of_approximation`):
the approximation proposition (`EnlargedApproximation`), `FiniteRH`, the continuous
main-term bound `BoundaryMainTermBound`, P7 and the analytic P4/P5 comparisons; confinement and the
boundary certificate are theorems from these. The full list of P8 gates, all
required domain and time-cell transfers, and the finite-head propagation P2c are
proved. The boundary main-term assumption is not a formalized grid certificate;
the polynomial computation and its Taylor-error bridge remain unproved in Lean.

The analytic estimates and the finite-RH/tail literature statements are not
inserted as project axioms. They remain explicit proposition arguments to Lean
theorems. Their conventional proofs and citations are part of the paper.
See [VERIFICATION.md](VERIFICATION.md) for precisely what each command establishes.
