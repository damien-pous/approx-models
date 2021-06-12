(** * Packing everything together into a tactic *)

Require Export String.
Require Export interfaces.
Require Import intervals syntax rescale errors.
Require taylor chebyshev approx.


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

(** tactic parameters *)
Inductive params :=
| i_deg of Z                                             (** interpolation degree *)
| i_float53 | i_bigint53  | i_z53 | i_bigint128 | i_z128 (** floating point implementation *)
| i_nbh of NBH                                           (** or direct choice of neighborhood implementation *)
| i_vm | i_native                                        (** native or vm computations *)
| i_dynamic | i_static(a b: Q) | i_static11.             (** dynamic/static semantics *)

Ltac get_deg x y :=
  lazymatch x with
  | tt => constr:(10%Z)
  | i_deg ?z => constr:(z)
  | (?p,?q) => get_deg p constr:((q,y))
  | _ => get_deg y tt
  end.

Ltac get_native x y :=
  lazymatch x with
  | i_native => constr:(true)
  | i_vm => constr:(false)
  | tt => constr:(false)
  | (?p,?q) => get_native p constr:((q,y))
  | _ => get_native y tt
  end.
Ltac get_nbh x y :=
  lazymatch x with
  | tt => constr:(Ifloat53.nbh)
  | i_float53 => constr:(Ifloat53.nbh)
  | i_bigint53 => constr:(IBigInt53.nbh)
  | i_z53 => constr:(IZ53.nbh)
  | i_bigint128 => constr:(IBigInt128.nbh)
  | i_z128 => constr:(IZ128.nbh)
  | i_nbh ?N => constr:(N)
  | (?p,?q) => get_nbh p constr:((q,y))
  | _ => get_nbh y tt
  end.

Ltac get_check nbh x y :=
  lazymatch x with
  | tt => constr:(Dynamic.check (N:=nbh) chebyshev_model)
  | i_dynamic => constr:(Dynamic.check (N:=nbh) chebyshev_model)
  | i_static ?a ?b => constr:(Static.check (N:=nbh) (chebyshev_model (DQ2 a b)))
  | i_static11 => constr:(Static.check (N:=nbh) chebyshev11_model)
  | (?p,?q) => get_check nbh p constr:((q,y))
  | _ => get_check nbh y tt
  end.

Ltac get_Sem nbh x y :=
  lazymatch x with
  | tt => constr:(Dynamic.Sem' (N:=nbh) chebyshev_model_ops)
  | i_dynamic => constr:(Dynamic.Sem' (N:=nbh) chebyshev_model_ops)
  | i_static ?a ?b => constr:(Static.Sem' (N:=nbh) (chebyshev_model_ops (fromQ a) (fromQ b)))
  | i_static11 => constr:(Static.Sem' (N:=nbh) chebyshev11_model_ops)
  | (?p,?q) => get_Sem nbh p constr:((q,y))
  | _ => get_Sem nbh y tt
  end.

(*
Goal True.
  let d := get_deg (i_float,i_deg 6, i_native) tt in pose d.
  let d := get_native (i_deg 6, i_native, i_prec 5) tt in pose d.
  let d := get_kind (i_deg 6, i_bigint, i_prec 5) tt in pose d.
 *)

(** helpers for the tactics below *)
Ltac ecomp native X :=
  match native with true => eval native_compute in X | false => eval vm_compute in X end.
Ltac comp native X :=
  match native with true => native_compute in X | false => vm_compute in X end.
Ltac cast native b :=
  match native with true => native_cast_no_check b | false => vm_cast_no_check b end.

(** ** tactic to prove bounds on concrete expressions *)
Tactic Notation "approx" constr(params) :=
  let deg := get_deg params tt in
  let native := get_native params tt in
  let nbh := get_nbh params tt in
  let check := get_check nbh params tt in
  lazymatch goal with |- ?p =>
  let p := reify_prop p in
  let t := constr:(check deg p) in
  (apply t || fail 100 "bug in reification? (please report)");
  [ repeat (constructor; auto) |
  let X := fresh "X" in
  intro X; comp native X;
  lazymatch eval hnf in X with
  | err ?s => fail 100 s
  | ret true => cast native (eq_refl true)
  | ret false => fail 100 "could not validate this, try increase degree"
  end ]
  end.
Tactic Notation "approx" := approx tt.


(** tactic to estimate certain real valued expressions 
    (do not change the goal -> turn these into commands?) *)
Tactic Notation "estimate" constr(e) constr(params) :=
  let deg := get_deg params tt in
  let native := get_native params tt in
  let nbh := get_nbh params tt in
  let Sem := get_Sem nbh params tt in
  let e := reify_real e in
  let t := constr:(Sem deg REAL e) in
  let i := ecomp native t in
  idtac i.
Tactic Notation "estimate" constr(e) := estimate e tt.

(* simple tests for the above tactics *)
(*
Goal 1.4 <= sqrt 2 <= 1.5.
Proof.
  approx. 
  Restart.
  approx (i_deg 15).
  Restart.
  approx (i_static11).
  Restart.
  approx (i_static11, i_deg 15).
  Restart.
  approx (i_static 0.5 2, i_z53).
  Restart.
  approx (i_static 0.5 2, i_nbh IZ128.nbh).
  (* static (DF2 0.5%float 2%float) (i_deg 15). *)

  Restart.
  estimate (sqrt 2).
  estimate (sqrt (-2)).
  estimate (RInt (@sqrt _) 1 2).
  estimate (RInt (@sqrt _) 1 2) (i_deg 3, i_bigint128, i_native).
  estimate (RInt id 0 1) (i_static11).
  estimate (RInt id 0 2) (i_static (-1) 3).
  estimate (RInt (@sqrt _) (-1) 1).
Abort.
*)
