(** * Packing everything together into a tactic *)

Require Export String.
Require Export interfaces.
Require Import intervals syntax rescale errors.
Require taylor chebyshev approx.

(* TODO: 
   - reification 
   - choice of interval implementation
*)

Section s.
 Context {N: NBH}.

 Definition chebyshev11_model_ops: ModelOps := approx.model_ops chebyshev.basis11_ops.
 Definition chebyshev11_model
   : Model chebyshev11_model_ops (-1) 1
   := approx.model chebyshev.basis11.

 Definition taylor_model_ops A B: ModelOps := approx.model_ops (taylor.basis_ops A B).
 Definition taylor_model (D: Domain)
   : Model (taylor_model_ops dlo dhi) dlo dhi
   := approx.model (taylor.basis D).

 Definition chebyshev_model_ops A B: ModelOps := approx.model_ops (chebyshev.basis_ops A B).
 Definition chebyshev_model (D: Domain)
   : Model (chebyshev_model_ops dlo dhi) dlo dhi
   := approx.model (chebyshev.basis D).

End s.

(** a user-defined tactic to prove bounds on concrete expressions *)
Tactic Notation "gen_bound" uconstr(bound) uconstr(e) constr(d) :=
  let f := constr:(bound d e) in
  (apply f || fail "the given expression does not match the goal");
  let X := fresh "X" in
  intro X; vm_compute in X;
  lazymatch eval hnf in X with
  | err ?s => fail 1 s
  | ret ?x => cbv; (lra || fail "could only obtain interval" x)
  end.

(** by default: chebyshev, with primitive floats by default *)
Tactic Notation "static" uconstr(D) uconstr(e) constr(d) :=
  gen_bound (Static.bound (chebyshev_model D)) e d.

(** interpolation degree: 10 by default *)
Tactic Notation "static" uconstr(D) uconstr(e) :=
  static D e (10%Z).

(** specific case: on [-1;1] *)
Tactic Notation "static11" uconstr(e) constr(d) :=
  gen_bound (Static.bound chebyshev11_model) e d .
Tactic Notation "static11" uconstr(e) := static11 e (10%Z).


(** by default: chebyshev, with primitive floats by default *)
Tactic Notation "dynamic" uconstr(e) constr(d) :=
  gen_bound (Dynamic.bound chebyshev_model) e d.
Tactic Notation "dynamic" uconstr(e) :=
  dynamic e (10%Z).


(* simple test for the above tactics
Goal 1.4 <= sqrt 2 <= 1.5.
Proof.
  dynamic (sqrt (fromZ 2)).
  Restart.
  dynamic (sqrt (fromZ 2)) 15%Z.
  Restart.
  static11 (sqrt (fromZ 2)).
  Restart.
  static11 (sqrt (fromZ 2)) 15%Z.
  Restart.
  static (DF2 0.5%float 2%float) (sqrt (fromZ 2)).
  Restart.
  static (DF2 0.5%float 2%float) (sqrt (fromZ 2)) 15%Z.
Qed.
*)
