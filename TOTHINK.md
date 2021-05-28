## TODO list

before the first release:

- document examples.v
- pointed uniform spaces for coquelicot 3.2.0

- choice of interval implementation by types and canonical structures
- further improve syntax/reification (degrees, eval)
- clean hints for rel / check cases not working
- support model comparisons in the synatx/tactic 


after the first release

- parameterised bounds (tests de positivité par oracle)
- side-conditions left to the user (mcontinuous)
- more functions on reals from coq-interval
- interpolation oracle for Taylor basis


tactic parameters:
- basis (chebyshev/taylor)
- domain (dynamic/static D)
- degree
- floats (primitive, bigint, bigZ)
- native vs vm




## questions for Guillaume:
- 1+1<>2 in primitive floats
- check functor applications in intervals.v




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

