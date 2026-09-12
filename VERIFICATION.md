# Verification scope

The paper is a conventional computer-assisted argument with a partial Lean
formalization. Published theorems are cited at their exact scopes. New analytic
deductions are written proofs supported by rigorous finite interval calculations.
Lean verifies a conditional theorem whose hypotheses are printed by
`lean/Audit.lean`; its axiom list does not discharge those hypotheses.

## Numerical reproduction

From the repository root:

~~~sh
python verify.py --regenerate
~~~

This verifies release integrity and support-input identities, checks generated
Lean data without changing them, and runs:

| Check | Required coverage |
|---|---|
| Exact barrier | 7849 reference + 4817 main rows; 1620 wall cells; 26 source boxes |
| P8, Arb | 7849 density floors + 6317 signed jet ceilings, 512 bits |
| P8, mpmath | The same inequalities, 80 decimal digits |
| Finite-sum matrix | 3844 complex coefficients from all 690950 terms, freshly regenerated |
| Finite boundary | 800000 closed cells covering \(t\in[0,1/5]\), \(y\in[0,1]\), at \(x=X\) |
| Direct source cross-check | Two specified corner points, original sums with 690950 terms per branch |
| Three-probe source | All 26 closed boxes and 78 bands, 384 bits |
| Density | 855 initial leaves, 1620 bottom cells and 1620 wall rows |
| Jet | 400 initial cells, top/head bounds, and exact geometry of 162 boundary boxes |
| Early jet boundary | All 45 boxes |
| Late jet boundary | All 117 boxes, each with nine center and nine wide cutoff bands |

Each late box runs in a fresh process. Their exact index union is 45–161.
Incomplete ranges, mismatched geometry, and partial outputs cannot count as
completion.

Without `--regenerate`, the command uses the distributed matrix but recomputes
every boundary cell. Its provenance and regeneration source are supplied.
`--quick` explicitly omits the supporting source/field/head computations.
No mode infers an analytic theorem from a saved pass string.

Supporting programs reject ambiguous interval inequalities. Assertion-based
programs refuse optimized Python. Tests exercise missing rows, incorrect joins,
box containment, strict-speed equality, malformed references, and disabled checks.
The native generator is also compiled with AddressSanitizer and
UndefinedBehaviorSanitizer for small first/last-index partitions, compared with
independent finite sums, and tested on invalid inputs and existing output paths.

## Formal verification

~~~sh
cd lean
python3 scripts/gen_data.py --check
lake exe cache get
lake build
lake env lean Audit.lean
~~~

Lean 4.33.1, mathlib v4.33.1, and leancert revision
`4ea18bb66dfcd7f18f260bc25302400f5a3cafd7` are pinned in the Lake files.
The audit fixes the numerical constant as well as the theorem name, prints the
premise structures, and rejects non-kernel proof dependencies in 14 principal
declarations. Its permitted foundational axioms are `propext`,
`Classical.choice`, and `Quot.sound`.

The formal development includes the complete rational barrier certificate,
barrier calculus, kernel inequalities, zero dynamics, first contact, the terminal
strip contraction, and exact profile/domain transfer. It checks four difficult
P8 gates: density rows 1251 and 3356, and jet rows 3356 and 5845. It also disproves
the erroneous extra-subtraction condition formerly printed for row 3356.
This limited numerical module does not establish all of P8.

The finite-head theorem, effective approximation, density/jet comparisons,
source-floor theorem, and all remaining P8 inequalities have not been proved in
Lean. Neither has the cited Polymath positive-time tail theorem; its confinement
corollary is formalized.

Use at least 32 GiB RAM for the complete Lean build. The rational-certificate
check reached roughly 15 GiB during preparation. The numerical GitHub workflow
runs on an ordinary hosted runner. The separate manual Lean workflow requires
a provisioned runner labelled `dbn-lean`, with elan and Python installed.

## Trust boundaries

Exact rationals require no rounding allowance. Arb and mpmath use enclosing
arithmetic and explicit analytic truncation bounds. The paper justifies the
extensions from finite computations to continuous boxes and unbounded cutoff
ranges; sampled values do not supply those extensions.

The numerical route trusts its analytic reductions and the behavior of Python,
C, their compilers, Arb/FLINT, mpmath, and the machine. The formal route has a
smaller proof-checking boundary but explicit unproved inputs. The encoded
statements must still agree with the intended mathematics.

Python package versions and Lean dependencies are pinned. The Docker base
filesystem is pinned by digest; native tool/library versions are recorded in
the runs. Native packages come from the specified distribution and can change
with its updates.

The supported numerical profile is CPython 3.12 with the hash-pinned
python-flint stable-ABI wheel. An intermittent exception occurred in the
CPython 3.14 environment during preparation; that failed run is not accepted
evidence, and its cause has not been established. The release does not claim
support for that profile. Independent late boxes use separate processes, with
every box and cutoff band still checked. This is an execution-profile choice,
not a relaxation of any mathematical condition.

The recorded preparation includes a complete replay in a fresh Ubuntu container
with networking disabled and the publication filesystem read-only. This is a
reproduction check of this package, not a general qualification of the host or
of unrelated historical native programs.

The manifest detects changed release files. It is not a signature, a proof of
an enclosure, or evidence of external expert acceptance.
