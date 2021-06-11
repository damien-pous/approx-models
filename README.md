**A certificate-based approach to formally verified approximations**

This is a Coq library to verify rigorous approximations of univariate
functions on real numbers. Based on interval arithmetic, this library
also implements a technique of validation a posteriori based on the
Banach fixed-point theorem. We moreover provide an implementation of
verified Chebyshev approximations.

**Authors**

Florent Bréhard, Assia Mahboubi, Damien Pous

**Requirements**

Coq 8.13 with libraries interval, coquelicot 3.2.0

**Description**

For more details, see the corresponding [article](https://hal.laas.fr/hal-02088529), published in the proceedings of the ITP 2019 conference.

* General purpose libraries, complementing coquelicot
  + `cball.v` : closed balls in uniform spaces
  + `posreal_complement.v` : canonical structure based automation for automating manifest positivity (resp. non-negativity) proofs
  + `domfct.v` : instance of uniform space structure for functions restricted to a subtype
  + `banach.v` : proof of the Banach fixedpoint theorem


* Abstractions for approximations
  + `interfaces.v` : hierarchy of abstractions: basic operations, neighborhoods, operations on functions
  + `vectorspace.v` : abstractions for generalized polynomials and linear combinations thereof, used for approximations
  + `rescale.v` : affine rescaling for a basis of generalized polynomials
  

* Instances of approximations
  + `intervals.v` : a simple instance of neighborhoods based on intervals with floating point endpoints
  + `chebyshev.v` : Chebyshev basis, for Chebyshev models
  + `taylor.v ` : monomial basis, for Taylor models


* Instances of certificate based approximations for elementary functions
  + `div.v` : Newton method for division
  + `sqrt.v` : Newton method for square root
  + `approx.v` : rigorous approximation in monomial basis, for division and square root

* High-level tactic
  + `syntax.v` : Syntax of the supported expressions
  + `tactic.v` : Tactic for certifying bounds

* Examples and benchmarks
  + `examples.v` : basic examples on how to use the library
  + `tests.v` : tests for the library
  + `example_abs.v` : tests for approximating the function [abs], as discussed in the the ITP19 paper
  + `example_h16.v` : computation of Abelian integrals related to Hilbert 16th problem

**Axioms**

We do not introduce any axiom, but we need the ones used for Reals in Coquelicot:

ClassicalDedekindReals.sig_not_dec
ClassicalDedekindReals.sig_forall_dec
FunctionalExtensionality.functional_extensionality_dep
Classical_Prop.classic

Additionally, depending on the choice of interval implementation, axioms about machine 63 bits integers or primitive floating point numbers are used.
