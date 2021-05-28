## TODO list

- clean/document fourier.v
- rename bnd into hull, r... into ...R
- more examples / more doc in examples.v
- further improve syntax/reification (degrees, eval)
- better support for model comparisons in the syntax/tactic 
- side-conditions left to the user (mcontinuous)
- more functions on reals from coq-interval
- interpolation oracle for Taylor basis
- subdivision?
- uncertified but efficient F.cos and F.pi ?
- continuity (from Coquelicot) vs continuity_pt (from Reals.Ranalysis1)
- better radius heuristics for solutions of polynomial equations
- linear List.rev

## TOTHINK

- should we systematically truncate model multiplications, and how?
  cf. branch truncate-mult
  may help a lot to validate solutions of polynomial equations:
  there we use [taylor.eval'] on model ops, so that models may grow significantly
- modular approach to continuity and/or other properties?
- uniform notation for containments?
- reals from mathcomp-analysis -> integration for possibly non-continuous functions
- model composition?
  

## usages of certain functions

range:
- user ?
- mdiv/msqrt

Dom:
- meval, mintegrate, msqrt

dom:
- specification of range in bases
- definition of model containment
- specification of range in models
- specification of continuity for rmintegrate

DomE: Dom X -> contains X x -> dom x
rdom: dom x -> contains (bnd lo hi) x


mag: [-eps1;+eps2] -> max eps1 eps2
sym: [a;b] -> [-b;b] or [a;-a]
- mdiv/mssqrt

max
- mag

min
unused!

bnd:
- sym
- srange
- rdom (for generic range operation)

## reification

forall x, a<x<b -> P x
- if x occurs in complicated places, just approximate x by [a;b], and possibly subdivide
  -> reified via an HO binder
- otherwise, use mne/mlt on [a;b]
  -> reified via a Prop term with one variable


forall x, a<x<b -> f x < g x /\ forall y, c<y<d -> h x y < 1
-> either fix x=[a;b] and subdivide if necessary
-> or use mne/mlt on x, late-fixing y=[c;d] ? plausible...
