# A warrant for the `N = 8` Thomson problem, in Lean 4
Found by **Joseph Tooby-Smith** and **Alex Zughaid**.

License: Apache 2.0

**Edit (25/09/26):** The following paper was posted on arXiv https://arxiv.org/pdf/2609.22077 before we made this code public, but after Claude had produced a full solution. 

In this repository, we provide a formal check that the n = 8 case of the Thompson problem is solved uniquely by the square antiprism of a set height. It was found using Claude Fable 5.1 and Opus 5 with a Claude Max subscription. The human prompting involved was minimal and only related to technicalities in Lean, rather than any of the related mathematics. 

We do not call this a proof, but instead a warrant, to distinguish it from the meaning of a proof in the traditional sense (which is a human-written, human-readable, convincing argument that something is true). This is certainly not that. See [here](https://josephtoobysmith.com/math/2026/09/18/Warrants-dinosaur-bones-AI.html).

We have made this code public in the interest of open science; however, we have not yet publicized its existence, as we think it is only right to do so once we have digested the proof fully. We do not think any credit should be given for the work that is written in this file. Whilst this warrant is complete, we consider everything here to still be very much a work in progress. 

See [here](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Proving.20an.20open.20conjecture.20with.20AI.20.2B.20Lean/with/625173451) for a discussion on proven open conjectures with AI and Lean and what to do with such results.


We believe that the N = 7 case was followed trivially from similar techniques. 

## Key references

Below is a list of AI-generated references that are believed to be used in the development of this warrant. Unfortunately, at this stage, we cannot assume that this list of references is 100% inclusive. 

**The problem**
- J. J. Thomson, *On the structure of the atom*, Philosophical Magazine **7** (1904), 237–265.
- T. Erber and G. M. Hockney, *Equilibrium configurations of N equal charges on a sphere*, J. Phys. A **24** (1991), L1369. (Numerical evidence for the square antiprism at `N = 8`.)

**Linear-programming (two-point) bounds** — [`Thomson/LP`](Thomson/LP)
- I. J. Schoenberg, *Positive definite functions on spheres*, Duke Math. J. **9** (1942), 96–108.
- P. Delsarte, J. M. Goethals and J. J. Seidel, *Spherical codes and designs*, Geom. Dedicata **6** (1977), 363–388.
- V. A. Yudin, *Minimum potential energy of a point system of charges*, Discrete Math. Appl. **3** (1993), 75–81 (Russian original: Diskret. Mat. **4** (1992)).

**Three-point (SDP) bounds** — [`Thomson/ThreePoint`](Thomson/ThreePoint)
- C. Bachoc and F. Vallentin, *New upper bounds for kissing numbers from semidefinite programming*, J. Amer. Math. Soc. **21** (2008), 909–924.
- H. Cohn and J. Woo, *Three-point bounds for energy minimization*, J. Amer. Math. Soc. **25** (2012), 929–958.

**Validated numerics** — [`Thomson/Numerics`](Thomson/Numerics)
- R. E. Moore, *Interval Analysis*, Prentice-Hall, 1966.
- K. Makino and M. Berz, *Taylor models and other validated functional inclusion methods*, Int. J. Pure Appl. Math. **4** (2003), 379–456.

**Related work**
- H. Cohn and A. Kumar, *Universally optimal distribution of points on spheres*, J. Amer. Math. Soc. **20** (2007), 99–148.
- R. E. Schwartz, *The five-electron case of Thomson's problem*, Exp. Math. **22** (2013), 157–186.
