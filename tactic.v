(** * Packing everything together into a tactic *)

Require Export String.
Require Export interfaces.
Require Import intervals syntax rescale errors.
Require taylor chebyshev approx.

(* TODO: reification *)

(** a user-defined tactic to prove bounds on concrete expressions *)
Tactic Notation "bound" uconstr(e) constr(d) constr(M) :=
  let f := constr:(@bound _ M d e) in
  (apply f || fail "the given expression does not match the goal");
  [ (now vm_compute) || fail "potential division by zero or square root of a negative value"
  | let X := fresh "X" in
    intro X; vm_compute in X;
    lazymatch eval hnf in X with
    | err ?s => fail 1 s
    | ret ?x => cbv; (lra || fail "could only obtain interval" x)
    end].

(** by default: chebyshev on [-1;1], with primitive floats by default *)
Tactic Notation "bound" uconstr(e) constr(d) :=
  bound e d (approx.model chebyshev.basis).

(** interpolation degree: 10 by default *)
Tactic Notation "bound" uconstr(e) :=
  bound e (10%Z).

