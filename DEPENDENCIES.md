# Proof dependencies

All functions and domains are defined in the [main paper](manuscript/main.md).
These are mathematical inputs, not acceptance flags.

| Input | Scope | Proof or source | Executable evidence |
|---|---|---|---|
| Classical heat flow and zero dynamics | Concrete integral, regularized zero sums, branch velocity and backward splitting | Polymath [Po19], Section 3; `DBN.External`, `ZeroBranch`, `Hermite`, `PairSum` | Lean kernel |
| Strip contraction | Strip half-width \(h\) at \(t\) gives real zeros at \(t+h^2/2\) | de Bruijn; Polymath Theorem 3.2; `DBN.External` | Lean kernel |
| P3a: confinement | One real-part bound on a compact positive-time interval | Polymath Theorem 1.5(i); \(R=e^{C/\tau}\) | Lean proves the corollary from an explicit literature parameter |
| P3b: approximation | \(x\ge5.9\cdot10^{12}\), \(0\le t\le1/5\), \(0\le y\le7\) | Appendix A.1–A.3; generic-real-part Arias de Reyna expansion | `support/fields/check_h7.py` |
| P2: finite head | Every zero with \(|\Re z|\le5999347341500\) is real, \(0\le t\le1/5\) | Appendix C; Platt–Trudgian Theorem 1; boundary and homotopy | `support/head/` matrix regeneration, full grid, direct sums |
| P4: density | \(S\ge U_Y/U-e^{90t}/10^{14}\), \(x\ge X\), \(\sqrt{q_M(t)}<Y\le5\) | Appendix A, coupled density/wall comparison | `check_m3a.py`: 855 initial leaves, 1620 bottom cells and wall rows |
| P5: jet | \(J\le C\), \(x\ge X\), \(\sqrt{q_M(t)}+3/5\le Y\le5\) | Appendix A, differential inequality and boundary proof | `check_fixed_c.py`, `check_early_boundary.py`, `check_late_boundary.py` |
| P7: source | \(V>L\), all \(x\ge X\), on each closed source box | Appendix C.3; P3b and elementary Dirichlet-series bounds; no wall or jet input | `support/source/verify.py`: all 26 boxes and 78 probes |
| P8: profile values | \(s+10^{-5}<U_Y/U\); signed jet ceiling at each reference cell | Main Section 4; `DBN.Profile` and `FieldTransfer` | All rows with two arithmetic libraries; four selected gates also in Lean |
| Barrier comparison | 4817 main rows, 7849 reference rows; terminal height \(1/400\) | Main Sections 5–7; `DBN.Certificate`, `FirstContact`, `Main` | Exact Python checks and Lean kernel |

P4 and P5 hold throughout \(0\le t\le T_M\). Their full quantifiers are printed
in the paper and formal premise structure.

The useful order is: P3b supplies the finite-head and source estimates; P3b and
the finite head supply the coupled density/wall comparison; these supply the
jet comparison; the profile gates and source floors supply the final barrier
comparison. The source floors are independent of the density and jet fields.
First contact uses the separate published confinement theorem.

The exact support-data identities are checked by `certificate/check_support.py`.
The JSON-to-Lean translation is checked by `lean/scripts/gen_data.py --check`.
No prior proposed bound or campaign acceptance decision is an input.

## Formal boundary

The original interface is
`RemainingPremises → Lambda ≤ bound`.
The additional interface is
`PolymathPositiveTimeRealTail → ProfileRemainingPremises → Lambda ≤ bound`.
It separates P2, P7, the analytic P4/P5 comparisons, and the full list of P8
gates. All required domain and time-cell transfers are proved.

The analytic estimates and the finite-RH/tail literature statements are not
inserted as project axioms. They remain explicit proposition arguments to Lean
theorems. Their conventional proofs and citations are part of the paper.
See [VERIFICATION.md](VERIFICATION.md) for precisely what each command establishes.
