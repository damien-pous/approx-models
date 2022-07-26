## TODO list

- document fourier.v
- more examples / more doc in examples.v
- further improve syntax/reification (eval, quantifiers)
- side-conditions left to the user (mcontinuous)
- more functions on reals from coq-interval
- interpolation oracle for Taylor basis
- better radius heuristics for solutions of polynomial equations

## TOTHINK

- modular approach to continuity and/or other properties?
- uniform notation for containments?
- reals from mathcomp-analysis -> integration for possibly non-continuous functions
- continuity (from Coquelicot) vs continuity_pt (from Reals.Ranalysis1)
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
domE: dom x -> contains (interval lo hi) x


mag: [-eps1;+eps2] -> max eps1 eps2
sym: [a;b] -> [-b;b] or [a;-a]
- mdiv/mssqrt

max
- mag
- mintegrate

min
- mintegrate

interval:
- sym
- srange
- domE (for generic range operation)

