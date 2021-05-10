(** * Packing everything together into a tactic *)

Require Export String.
Require Export interfaces.
Require Import intervals syntax rescale errors.
Require taylor chebyshev approx.

(* TODO: 
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

(** ** tactic to prove bounds on concrete expressions *)
Tactic Notation "gen_check" uconstr(check) constr(d) :=
  lazymatch goal with |- ?p =>
  let p := reify_prop p in
  let t := constr:(check d p) in
  (apply t || fail "bug in reification? (please report)");
  [ repeat (constructor; auto) |
  let X := fresh "X" in
  intro X; vm_compute in X;
  lazymatch eval hnf in X with
  | err ?s => fail 1 s
  | ret true => reflexivity
  | ret false => fail "could not validate this, try increase degree"
  end ]
  end.

(** by default: chebyshev, with primitive floats by default *)
Tactic Notation "static" uconstr(D) constr(d) :=
  gen_check (Static.check (chebyshev_model D)) d.

(** interpolation degree: 10 by default *)
Tactic Notation "static" uconstr(D) :=
  static D (10%Z).

(** specific case: on [-1;1] *)
Tactic Notation "static11" constr(d) :=
  gen_check (Static.check chebyshev11_model) d .
Tactic Notation "static11" := static11 (10%Z).


(** by default: chebyshev, with primitive floats by default *)
Tactic Notation "dynamic" constr(d) :=
  gen_check (Dynamic.check chebyshev_model) d.
Tactic Notation "dynamic" :=
  dynamic (10%Z).


(** tactics to estimate certain real valued expressions 
    (do not change the goal -> turn these into commands?) *)
Tactic Notation "gen_estimate" uconstr(Sem) constr(d) constr(e) :=
  let e := reify_real e in
  let t := constr:(Sem d REAL e) in
  let i := eval vm_compute in t in
  idtac i.
Tactic Notation "static_est" uconstr(lo) uconstr(hi) constr(d) constr(e) :=
  gen_estimate (Static.Sem' (chebyshev_model_ops lo hi)) d e.
Tactic Notation "static_est" uconstr(lo) uconstr(hi) constr(e) :=
  static_est lo hi 10%Z e.

Tactic Notation "static11_est" constr(d) constr(e) :=
  gen_estimate (Static.Sem' chebyshev11_model_ops) d e.
Tactic Notation "static11_est" constr(e) :=
  static11_est 10%Z e.

Tactic Notation "dynamic_est" constr(d) constr(e) :=
  gen_estimate (Dynamic.Sem' chebyshev_model_ops) d e.
Tactic Notation "dynamic_est" constr(e) :=
  dynamic_est 10%Z e.

(* simple tests for the above tactics *)
(*
Goal 1.4 <= sqrt 2 <= 1.5.
Proof.
  dynamic.
  Restart.
  dynamic 15%Z.
  Restart.
  static11.
  Restart.
  static11 15%Z.
  Restart.
  static (DQ2 0.5 2).
  Restart.
  static (DF2 0.5%float 2%float) 15%Z.

  Restart.
  dynamic_est (sqrt 2).
  dynamic_est (sqrt (-2)).
  dynamic_est (RInt (@sqrt _) 1 2).
  static11_est (RInt id 0 1).
  static_est (fromZ 0) (fromZ 3) (RInt id 0 2).
  dynamic_est (RInt (@sqrt _) (-1) 1).
Abort.
*)
