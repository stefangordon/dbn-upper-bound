# Provenance and release information

The initial research and drafts were produced in September 2026 with AI
assistance. This preparation used Astra reviewers for independent mathematical
reconstruction, numerical replay, and formalization. Automated review is not
external peer review, and models are not listed as paper authors. Human authors
must take responsibility for the submitted argument.

## Preparation changes

- Replaced campaign acceptance records and unused trajectories with a compact
  rational certificate. Every generated Lean data declaration was compared with
  its predecessor; all mathematical bytes were identical.
- Rebuilt the boundary matrix from its finite sums and checked the entire
  800000-cell vertical boundary directly, replacing the earlier split
  low-boundary and winding-number routes.
- Recomputed all 26 source floors through a single normalization argument that
  proves non-vanishing directly, removing dependence on the density/jet wall.
- Recomputed initial density, lower-boundary, initial jet, and every early/late
  jet-boundary estimate.
- Corrected backward Hermite splitting, reciprocal-zero summation, profile
  monotonicity, and an extra density subtraction. The exact bound and
  accepted rational gates did not change.
- Added exact Lean profile/domain transfers, a literature interface for
  confinement, selected difficult P8 checks, and a kernel refutation of the
  formerly printed stronger P8 condition.
- Added adversarial tests, complete-range checks, a reproduction image, a typeset
  paper, and an integrity-checked release exporter.
- Proved every P8 endpoint gate in Lean with a verified rational fixed-point
  evaluator (`lean/DBN/GateChecker.lean`), removing the P8 gate list from the
  explicit premise interface.
- Proved finite-head propagation in Lean (`lean/DBN/Head.lean`, with
  `ZeroCount.lean`, `HermiteRoots.lean` and `HermiteForward.lean`): P2 follows
  from the finite-RH input at `t = 0` and boundary nonvanishing. The original
  main interface's full head field is preserved; the approximation interface
  supplies it through this theorem.
- Exposed the enlarged approximation and continuous boundary main-term bound
  as explicit unproved inputs (`lean/DBN/Approximation.lean`), and proved their
  boundary-nonvanishing consequence and a scalar error threshold. This does
  not formalize the finite polynomial grid or its Taylor-error bridge.
- Proved positive-time confinement from Lemma A.1 alone in Lean
  (`lean/DBN/ConfineApprox.lean`, with the reflected-coefficient bound proved from
  the definitions in `lean/DBN/GammaEstimate.lean`) and added the approximation
  interface `DBN.lambda_le_bound_of_approximation`, which uses no literature tail
  theorem.
- Proved three ingredients of the source recipe in Lean: the Euler-product lower
  bound for `|ζ(s)|` and the termwise common-phase inequality (C25)
  (`lean/DBN/ZetaBounds.lean`), and the nonnegative-coefficient Dirichlet series
  for `−ζ'/ζ − (t/4)(ζ''/ζ)'` (`lean/DBN/VonMangoldtSeries.lean`). The finite
  heat identity and remainder norm bounds are also proved in
  `lean/DBN/HeatIdentity.lean`. These are auxiliary results, not the complete
  uniform source-floor proof.
- Checked the native coefficient generator with memory/undefined-behavior
  instrumentation and independent small finite sums. Output failure paths now
  close files and release initialized objects before reporting failure.

The additional formalization was drafted with Claude Code assistance and
reviewed with Astra. Review corrected normalization and forward-time comments,
distinguished continuous assumptions from finite certificates, and preserved
the original main theorem's premise structure. Automated review is not external
peer review.

Earlier campaign records are preserved in the originating research workspace,
outside this standalone package. They are not mathematical inputs. The
preparation record identifies the original revision and an archived copy of
the previous package. No transcripts, credentials, virtual environments, or
compiled Lean dependencies are included in the release.

## External material

Classical and approximation sources are in the paper's
[references](manuscript/references.md). The finite-RH verification is the
published Platt–Trudgian theorem. Concurrent unrefereed work is distinguished
from established literature and is not a proof premise.

The Lean companion downloads [mathlib](https://github.com/leanprover-community/mathlib4)
and [leancert](https://github.com/alerad/leancert) at locked revisions. Both carry
Apache-2.0 licenses; their source and caches are not vendored. The numerical
environment installs python-flint, mpmath, and FLINT through their distributions
and licenses.

The C matrix generator and Python checkers are inspectable source. Recorded
outputs are observations for comparison with fresh runs, not premises read by
the checkers.

## Release metadata

The repository is [stefangordon/dbn-upper-bound](https://github.com/stefangordon/dbn-upper-bound).

The manuscript names Stefan Gordon as its author, as explicitly supplied by
the author. No affiliation, ORCID, or correspondence address has been inferred.
Release licensing remains a separate repository decision.

A public release should receive a stable tag and archival identifier when its
authors approve it. External peer review, priority assessment, and journal
acceptance remain separate from the local checks described here.
