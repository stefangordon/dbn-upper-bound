# Analytic field verification

These programs verify the finite inequalities used in
[Appendix A](../../manuscript/analytic-estimates.md).
They need Python and python-flint, at the versions specified by the package.
The programs do not import historical campaign code or read saved numerical
results. Their only data inputs are the two files in data/ and the canonical
certificate/data/old-M3a-wall.json.

Run the package's unified verifier for a full reproduction. Individual
commands, from this directory, are:

    python check_h7.py --output /tmp/h7.json
    python check_m3a.py --output /tmp/m3a.json
    python check_fixed_c.py --output /tmp/fixed-c.json
    python check_early_boundary.py --output /tmp/early.json
    python check_late_boundary.py --output /tmp/late.json

The first four computations take about a second altogether on the preparation
machine. The supported unified runner uses CPython 3.12 and starts a fresh
process for each late box: --start i --stop i+1 for every i from 45 through 161.
These adjacent half-open ranges have exact union [45,162); all mathematical
checks are unchanged. See the package's verification document for runtime
limitations. Each completed output has completed=true;
partial progress files have completed=false. A successful subset is not the
complete late-boundary certificate.

The H7, M3a and fixed-C programs use Arb512. Early and late boundary programs
default to --bits 512. No output is written unless an output path is supplied.
Every executable verifier explicitly refuses optimized Python, since its
assertions are mathematical gates.

The data are exact rational geometry, not sampled function values.
All complex-source estimates are reduced analytically to real ball enclosures
in Appendix A. In particular the final cutoff band is unbounded, the full
time intervals are enclosed before signed coefficients are bounded, and every
wide cutoff band contributes to the Cauchy derivative bound.

The adaptations and original digests are listed in provenance.json. The main
package manifest pins the published code and data. Neither a provenance entry
nor an old successful run supplies an unchecked mathematical premise.
