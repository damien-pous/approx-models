## TODO list

- more examples / more doc in examples.v
- further improve syntax/reification (degrees, eval)
- better support for model comparisons in the syntax/tactic 
- side-conditions left to the user (mcontinuous)
- more functions on reals from coq-interval
- interpolation oracle for Taylor basis
- choice of basis in the tactic
- subdivision?
- uncertified but efficient F.cos and F.pi ?
- continuity (from Coquelicot) vs continuity_pt (from Reals.Ranalysis1)


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

