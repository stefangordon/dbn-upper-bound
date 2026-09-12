# Uniform three-probe source estimates

From the publication root:

```sh
python support/source/verify.py
```

Use the pinned CPython 3.12 environment with `python-flint==0.9.0`.
The computation uses 384 bits and recomputes every bound for
all **26 closed boxes and 78 probe bands** in [`boxes.json`](boxes.json).
It reads no saved source enclosures. Optional `--output NEW.json` saves a fresh
record; an existing output is refused. The default writes no files.

For each box the asserted conclusion is

`(15/14)S(x,3h,t) - (16/21)S(x,4h,t) + (1/6)S(x,5h,t) > floor`

for every point of that closed time/height rectangle and every
`x>=5999347341500`, with every actual cutoff
`N=floor(sqrt(x/(4*pi)+t/16))>=690950`.
The boxes are consumed separately; their Cartesian hull is not certified.
The exact quantifiers and reduction to these computations are proved in
[computational-estimates.md](../../manuscript/computational-estimates.md).

The calculation includes the 1024-term heat head, 1024 consecutive logarithmic
integral cells and an explicit tail to infinity, four ordinary power/logarithm
tails, the reflected prefix with both endpoint terms and an analytic reduction
for every `N>=690950`, both changed-cutoff terms on each analytic source disk,
the first Cauchy derivative allowance, and all normalization and common-phase
costs. The middle probe's negative weight stays inside the coherent signed
expression. Every acceptance gate uses a certain ball inequality.

Only the additive denominator route is needed: a strict defect below one
proves that `H_t/B_t` is nonzero at each centre and bounds its logarithmic
derivative error directly. Thus this source proof has **no wall or jet-field
input**. Its analytic input is the effective H7 source theorem and the
archimedean estimates proved in `manuscript/analytic-estimates.md`.
In particular, no jet-field estimate is assumed on a disk crossing `x=X`.

[`results/replay.json`](results/replay.json) records every component of the
complete fresh calculation, including the strictly positive margins over all
published floors. This is a replay aid, not an input to `verify.py`. The original
screening target `72/25` was insufficient on boxes 05–25; those failures do not
enter this proof, which uses the exact lower floors stated in the paper.

The checker trusts FLINT/Arb's enclosures of elementary functions and real-zeta
Taylor coefficients. The analytic uniform-reduction proof and the effective
source theorem remain mathematical premises of the numerical computation;
neither a successful process nor a saved result formalizes them in Lean.
