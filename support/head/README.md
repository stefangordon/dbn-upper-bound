# Finite-head nonvanishing

`verify.py` recomputes all **800,000 closed rectangles** at the single exact
abscissa `X=5999347341500`, covering `0<=t<=1/5`, `0<=y<=1`. Each rectangle has
side lengths `1/2000`. It evaluates the unscaled Taylor source polynomial in
complex ball arithmetic and requires `abs(F_M)>0.002000000001` in every cell.
`bounds.py` recomputes the repaired H7 Lemma A.1's whole-domain source allowance
`0.00121580200259... < 0.001215803 < 1/500`, and the Taylor error below `1e-12`
on the entire physical domain. H7's derivation and scalar checks are shared
with the source and field estimates; the head uses no separate narrow-range
approximation theorem.

The proof connecting these computations to `H_t`, and the subsequent finite-RH
homotopy argument, is in
[computational-estimates.md](../../manuscript/computational-estimates.md).
This direct full-segment calculation replaces the separate low-segment and
winding-number calculations used during development.

From the publication root, using the pinned CPython 3.12 environment:

```sh
python support/head/verify.py
python support/head/spotcheck.py
```

The default reads `data/matrix.txt`, the freshly regenerated 62-by-62 matrix
of complex balls. It does not read a previous pass/fail result. Its lowest
certified cell lower bound exceeded `1.2765849605`. The complete replay record is
[`results/replay.json`](results/replay.json). These margins concern the finite
approximation, and the two separately justified error bounds are subtracted
before concluding nonvanishing of `H_t`.

The second command independently sums the original source at the two corners
`(t,y)=(0,0)` and `(1/5,1)`, using all 690,950 terms in both branches at each
point. It agrees with the accelerated matrix expression within `2.81e-33` at
both points. This checks the normalization, matrix
factorization and conjugation; it is a two-point cross-check and does not
replace the full interval grid. Its record is
[`results/direct-sum.json`](results/direct-sum.json).

To regenerate every coefficient directly from its defining finite sum:

```sh
python support/head/regenerate.py --jobs 8 --output /tmp/dbn-matrix-new.txt
python support/head/verify.py --matrix /tmp/dbn-matrix-new.txt
```

Choose a new output name; existing outputs are refused. The generator requires
`gcc`, FLINT headers and the FLINT/GMP/MPFR libraries (`libflint-dev` on Debian
or Ubuntu). It compiles `generate-matrix.c` in a temporary directory, partitions
the 690,950 indices into disjoint consecutive ranges, computes at 192 bits,
and adds the partial matrices at 256 bits. All coefficient radii are retained.
The Python writer checks that each serialized enclosure contains the ball
before serialization. Neither regeneration nor checking uses a historical
matrix, a decimal table without radii, or a saved coefficient-error estimate.
The reproduction image uses CPython 3.12, python-flint 0.9.0 with bundled
FLINT 3.6.0, and a separately linked system FLINT for the C generator.
The recorded native package/compiler versions, timings, matrix and generator
hashes, exact partition and regeneration precision are in
[`data/matrix.provenance.json`](data/matrix.provenance.json).
The default replay still trusts that the supplied balls were produced by the
specified generator; running regeneration removes dependence on that stored
numerical input. Both routes trust the compiler, FLINT/Arb and the machine.

`--output NEW.json` optionally writes a fresh verification record. Without it,
verification prints the result and writes no files. The grid, error and
regeneration checkers reject Python's `-O` mode; the direct-sum checker uses
explicit exceptions. The external Platt–Trudgian finite-RH verification is cited
as a published theorem and is not rerun here. These calculations are not
Lean-kernel proofs.

The native-generator tests compile with AddressSanitizer and
UndefinedBehaviorSanitizer, check partitions at both index boundaries against
independent finite sums, and reject malformed ranges and existing output files.
They run as part of the repository's test suite and require the same C compiler
and FLINT development libraries as regeneration.
