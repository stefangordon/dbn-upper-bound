# References

**[dB50]** N. G. de Bruijn, *The roots of trigonometric integrals*, Duke Mathematical Journal **17** (1950), 197–226. The strip-contraction statement used here is also stated as [Po19, Theorem 3.2].

**[Ne76]** C. M. Newman, *Fourier transforms with only real zeros*, Proceedings of the American Mathematical Society **61** (1976), 245–251.

**[Po19]** D. H. J. Polymath, *Effective approximation of heat flow evolution of the Riemann xi function, and a new upper bound for the de Bruijn–Newman constant*, Research in the Mathematical Sciences **6** (2019), article 31. [arXiv:1904.12438v2](https://arxiv.org/abs/1904.12438v2). In particular: Theorems 1.3 and 1.5(i), Proposition 3.1, Theorem 3.2, and Proposition 6.2. Version 2 incorporates the published paper's referee corrections.

**[PT21]** D. Platt and T. Trudgian, *The Riemann hypothesis is true up to $3\cdot10^{12}$*, Bulletin of the London Mathematical Society **53** (2021), 792–797. [DOI:10.1112/blms.12460](https://doi.org/10.1112/blms.12460); [arXiv:2004.09765](https://arxiv.org/abs/2004.09765). Theorem 1 supplies the finite-RH input; Corollary 2 gives the upper bound $0.2$.

**[RT20]** B. Rodgers and T. Tao, *The de Bruijn–Newman constant is non-negative*, Forum of Mathematics, Pi **8** (2020), e6. [arXiv:1801.05914v5](https://arxiv.org/abs/1801.05914v5). The cited version includes the authors' subsequent corrections.

**[Ar11]** J. Arias de Reyna, *High precision computation of Riemann's zeta function by the Riemann–Siegel formula, I*, Mathematics of Computation **80** (2011), 995–1009. [DOI:10.1090/S0025-5718-2010-02426-3](https://doi.org/10.1090/S0025-5718-2010-02426-3). The coefficient bounds used here are restated in [Po19, Proposition 6.2].

**[Jo17]** F. Johansson, *Arb: Efficient arbitrary-precision midpoint-radius interval arithmetic*. [arXiv:1611.02831](https://arxiv.org/abs/1611.02831). The numerical programs use Arb through python-flint; the C coefficient generator uses the FLINT library directly.

**[Go26]** J. Gomila, *A computer-assisted proof of $\Lambda\le0.1787854$*, public manuscript and repository, 2026. [Repository](https://github.com/judegomila/dbn-lambda-01787854-candidate-audit). Accessed 11 September 2026; the author describes the work as not yet peer reviewed. This concurrent claim is cited for context and is not a proof dependency.

**[Lean]** The Lean community, [Lean 4](https://github.com/leanprover/lean4) and [mathlib](https://github.com/leanprover-community/mathlib4), versions 4.33.1. Exact revisions are recorded in the companion project's Lake manifest.

**[LC]** [leancert](https://github.com/alerad/leancert), revision 4ea18bb66dfcd7f18f260bc25302400f5a3cafd7. The companion imports its heat-flow analysis and uses its kernel-mode interval evaluator. Imported definitions are connected to the paper's heat integral by proved equalities.
