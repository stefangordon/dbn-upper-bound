# de Bruijn–Newman upper bound


**[Read the paper (PDF)](output/pdf/dbn-upper-bound.pdf)** · [Paper source](manuscript/main.md) · [Verification guide](VERIFICATION.md)

Paper, exact certificates, reproducible computations, and a partial Lean 4
formalization of the computer-assisted bound:

```math
\begin{aligned}
\Lambda &\le
\frac{3885632262767861213460393068710302759}
     {24646172707879668706230182733520000000} \\
&= 0.157656619095490606768\ldots < 0.158.
\end{aligned}
```

The proof combines the published Platt–Trudgian finite-RH theorem with new
analytic estimates and rigorous interval computations.

> **Verification scope.** The Lean theorem is conditional on explicit analytic
> inputs; this is not a complete formal proof of the numerical bound. The paper
> has not undergone external peer review.

## Reproduce the numerical evidence

With Docker:

~~~sh
docker build --tag dbn-verification .
docker run --rm dbn-verification --regenerate
~~~

This regenerates the finite-sum coefficient matrix, checks every boundary cell,
recomputes all source and field estimates, and verifies the exact barrier and
profile inequalities. Allow several minutes. No network is used by the checks
after the image has been built.

The tested image is Linux x86_64 with CPython 3.12 and hash-pinned numerical
wheels. Alternatively, use that same Python version with a C compiler and FLINT headers:

~~~sh
sudo apt-get install python3-venv gcc libc6-dev libflint-dev libgmp-dev libmpfr-dev
python3.12 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
.venv/bin/python verify.py --regenerate
~~~

The explicit shortcut `python verify.py --quick` runs only the finite
barrier/profile checks and input identities. Running without `--regenerate`
checks all components but uses the supplied boundary matrix. Every mode states
its scope. See [verification scope](VERIFICATION.md).

## Check the formal companion

Install [elan](https://github.com/leanprover/elan) and run:

~~~sh
cd lean
lake exe cache get
lake build
lake env lean Audit.lean
~~~

Use a machine with at least 32 GiB RAM. Full kernel reduction of the rational
certificate took about 13 minutes and reached roughly 15 GiB on the preparation
machine. The [Lean guide](lean/README.md) gives the exact theorem interfaces,
dependency pins, and remaining assumptions.

## Read the proof

| Material | Contents |
|---|---|
| [Main paper](manuscript/main.md) | Definitions, certificate, force inequalities, first-contact proof |
| [Appendix A](manuscript/analytic-estimates.md) | Effective approximation, density and jet comparisons, boundary estimates |
| [Appendix B](manuscript/source-boxes.md) | All 26 exact source boxes and floors |
| [Appendix C](manuscript/computational-estimates.md) | Finite head and uniform three-probe source proof |
| [Dependency map](DEPENDENCIES.md) | Which statement supplies each input |
| [Verification scope](VERIFICATION.md) | Commands, expected coverage, numerical and formal trust boundaries |
| [Provenance](PROVENANCE.md) | AI assistance, preparation changes, external dependencies, release metadata |

Numerical code is under `certificate/` and `support/`; the formal development is
under `lean/`. No campaign environment, review transcript, optimizer, or earlier
candidate trajectory is required.

## Build the paper and prepare a release

The paper uses Pandoc and LuaLaTeX. On Debian/Ubuntu install `pandoc`,
`texlive-luatex`, `texlive-latex-extra`, `texlive-fonts-recommended`, and `fonts-dejavu-core`.

~~~sh
python scripts/build_paper.py
python scripts/manifest.py --write
python scripts/manifest.py
python -m unittest discover -s tests -v
python scripts/export.py /path/to/new-repository --archive /path/to/new-release.tar.gz
~~~

The exporter checks the inventory and refuses existing destinations. It includes
the paper and exact sources, and excludes build caches and local environments.
The generated LaTeX source is in `build/paper/` after typesetting.
`MANIFEST.json` fixes file identities; it does not certify mathematical claims.
