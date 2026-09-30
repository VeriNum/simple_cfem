# Suggested improvements to Quadrature proofs

- There are many proofs in the form ``{in `[a,b], continuous f}`` that should perhaps be ``{within `[a,b]``; is it possible to use `within..continuous` everywhere?
- `Rintegral_gt_0` is proved in Saikawa's [P.R. #2086](https://github.com/math-comp/analysis/pull/2086); should that P.R. be merged into mathcomp-analysis or should we just copy-paste the proof into here?
- The Admitted lemma `quadrature_error` is incorrect.  Where it has `(2*n+2)`, the correct formula is `(2*n)`.  Solution: state the Taylor-Lagrange theorem explicitly (even if it's Admitted), then prove `quadrature_error` from Taylor-Lagrange.
- Just before the comment beginning `(** 15.  The Gaussian quadrature formula ... ` is a discussion of `the roots of a polynomial`.  Does this accurately describe limitations of mathcomp-analysis?
- The entire `extend_roots_injective` lemma would not be necessary if `mathcomp.algebra.qpoly.lagrange` were defined differently.  Instead of argument `(x: nat-> K)`, that function should take an argument `(x: nat -> 'I_n)`, then we wouldn't need this `extend_roots` hack.
- In some places, functions are proved derivable and continuous everywhere (from -\infty to \infty), where it would suffice to be derivable and continuous within [lo,hi].  Adjusting this would generalize quadrature so it is applicable to more functions.
- Does mathcomp-analysis have the Weierstrass approximation theorem?  If so, one could prove `quadrature_converges` (after correcting the theorem-statement).
- In `Module Legendre` I have instantiated Legendre polynomials up to degree 4.  There are two reasons for stopping here:
	- For my intended application in the Finite Element Method, degree 2 is the highest that is practically useful.
	- Legendre polynomials up to degree 4 have roots expressible as real-valued formulas in closed form (with addition, subtraction, multiplication, division, and square root); beyond that, there is no closed form.
- There are alternate approaches that would avoid the degree-4 restriction if that were considered useful:
	- Don't state the real roots at all.  Instead, for each floating-point near-root x, prove that `f(x-d)<0` and `f(x+d)>0`, where f is the Legendre polynomial of interest, and `round(x-d)=round(x+d)=x`.
	- That solution is annoying, because it brings floating-point into quadrature.v and quadrature2.v, which (until now) are purely in the real numbers.  So another solution is to exhibit constructive reals that are roots, as long as there is a way of proving that certain floating-point numbers are the correct roundings of those constructive reals.

