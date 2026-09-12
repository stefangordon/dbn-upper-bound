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
- Checked the native coefficient generator with memory/undefined-behavior
  instrumentation and independent small finite sums. Output failure paths now
  close files and release initialized objects before reporting failure.

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
