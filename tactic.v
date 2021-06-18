(** * Packing everything together into a tactic *)

Require Export String.
Require Export interfaces.
Require Import intervals syntax rescale.
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

(** ** tactic parameters *)
(** in each group, default value comes first *)
Inductive param :=
(** interpolation degree (default: 10) *)
| i_deg of Z
(** floating point implementation *)
| primfloat
| bigint60 | bigint120 | bigint300   
| stdz60 | stdz120
(** or direct choice of neighborhood implementation *)
| nbh of NBH
(** native or vm computations *)
| vm | native
(** dynamic/static semantics (and Chebyshev of [[-1;1]] as a special case of static semantics) *)
| dynamic | static(a b: Q) | chebyshev11
(** basis (be careful, chebyshev11 above takes precedence even when placed after [taylor] or [fourier] )*)
| chebyshev | taylor | fourier.             

(** lists of parameters are presented as tuples of tuples of tuples ... of elements in [param] 
    (e.g., [(bigZ60,((i_deg 5,vm), primfloat))])
    first occurrence of a parameter in a given group takes precedence
    (e.g., above, [bigZ60] takes precedence over [primfloat]) *)
Ltac is_param x :=
  match type of x with param => idtac | _ => fail 100 x "is not a valid parameter" end.
Ltac all_params x :=
  lazymatch x with
  | tt => idtac
  | (?p,?q) => all_params p; all_params q
  | ?p => is_param p
  end.

(*
Goal True.
  is_param primfloat.
  Fail is_param 4.
  check_params (primfloat,vm).
  Fail check_params (primfloat,true).
 *)

(** accessors for parameters:
    we explore parameters in Ltac with functions using the pattern below, where [x] is the main argument and [y] is an accumulator for the remaining arguments.
    [y] is supposed to be [tt] in the main call to the function, so that if we ever reach [tt], we return the default value.
*)
Ltac get_deg x y :=
  lazymatch x with
  | tt => constr:(10%Z)                 (* default value *)
  | i_deg ?z => constr:(z)              (* a specific parameter was given, use it *)
  | (?p,?q) => get_deg p constr:((q,y)) (* recurse on pairs *)
  | _ => get_deg y tt                   (* jump to the accumulator if [x] is a parameter from another group *)
  end.

Ltac get_native x y :=
  lazymatch x with
  | native => constr:(true)
  | vm => constr:(false)
  | tt => constr:(false)
  | (?p,?q) => get_native p constr:((q,y))
  | _ => get_native y tt
  end.

Ltac get_basis x y :=
  lazymatch x with
  | tt => constr:(tt)
  | chebyshev => constr:(chebyshev)
  | taylor => constr:(taylor)
  | fourier => constr:(fourier)
  | (?p,?q) => get_basis p constr:((q,y))
  | _ => get_basis y tt
  end.

Ltac get_nbh x y :=
  lazymatch x with
  | tt => constr:(IPrimFloat.nbh)
  | primfloat => constr:(IPrimFloat.nbh)
  | bigint60 => constr:(IBigInt60.nbh)
  | bigint120 => constr:(IBigInt120.nbh)
  | bigint300 => constr:(IBigInt300.nbh)
  | stdz60 => constr:(IStdZ60.nbh)
  | stdz120 => constr:(IStdZ120.nbh)
  | nbh ?N => constr:(N)
  | (?p,?q) => get_nbh p constr:((q,y))
  | _ => get_nbh y tt
  end.

Ltac get_model basis :=
  match basis with
    | tt => uconstr:(chebyshev_model)
    | chebyshev => uconstr:(chebyshev_model)
    | taylor => uconstr:(taylor_model)
    | fourier => fail 100 "fourier not yet integrated"
  end.
Ltac get_check nbh model x y :=
  lazymatch x with
  | tt => constr:(Dynamic.check (N:=nbh) model)
  | dynamic => constr:(Dynamic.check (N:=nbh) model)
  | static ?a ?b => constr:(Static.check (N:=nbh) (model (DQ2 a b)))
  | chebyshev11 =>
    (* match basis with *)
    (*   | taylor => idtac "warning, chebyshev11 takes precedence over taylor" *)
    (*   | fourier => idtac "warning, chebyshev11 takes precedence over fourier" *)
    (* end; *)
    constr:(Static.check (N:=nbh) chebyshev11_model)
  | (?p,?q) => get_check nbh model p constr:((q,y))
  | _ => get_check nbh model y tt
  end.

Ltac get_model_ops basis :=
  match basis with
    | tt => uconstr:(chebyshev_model_ops)
    | chebyshev => uconstr:(chebyshev_model_ops)
    | taylor => uconstr:(taylor_model_ops)
    | fourier => fail 100 "fourier not yet integrated"
  end.
Ltac get_Sem nbh model_ops x y :=
  lazymatch x with
  | tt => constr:(Dynamic.Sem' (N:=nbh) model_ops)
  | dynamic => constr:(Dynamic.Sem' (N:=nbh) model_ops)
  | static ?a ?b => constr:(Static.Sem' (N:=nbh) (model_ops (fromQ a) (fromQ b)))
  | chebyshev11 => constr:(Static.Sem' (N:=nbh) chebyshev11_model_ops)
  | (?p,?q) => get_Sem nbh model_ops p constr:((q,y))
  | _ => get_Sem nbh model_ops y tt
  end.

(*
Goal True.
  let d := get_deg (primfloat,i_deg 6, native) tt in pose d.
  let d := get_native (i_deg 6, native, primfloat) tt in pose d.
 *)

(** helpers for the tactics below *)
Ltac ecomp native X :=
  match native with true => eval native_compute in X | false => eval vm_compute in X end.
Ltac comp native X :=
  match native with true => native_compute in X | false => vm_compute in X end.
Ltac cast native b :=
  match native with true => native_cast_no_check b | false => vm_cast_no_check b end.

(** ** tactic to prove bounds on concrete expressions *)
(** see type [param] above for tactic parameters *)
Tactic Notation "approx" constr(params) :=
  all_params params;
  let deg := get_deg params tt in
  let native := get_native params tt in
  let nbh := get_nbh params tt in
  let basis := get_basis params tt in
  let model := get_model basis in
  let check := get_check nbh model params tt in
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
  end]
  end.
Tactic Notation "approx" := approx tt.


(** ** tactic to estimate certain real valued expressions *)
(** see type [param] above for tactic parameters *)
(* TOTHINK: do not change the goal -> turn these into commands? *)
Tactic Notation "estimate" constr(e) constr(params) :=
  all_params params;
  let deg := get_deg params tt in
  let native := get_native params tt in
  let nbh := get_nbh params tt in
  let basis := get_basis params tt in
  let model_ops := get_model_ops basis in
  let Sem := get_Sem nbh model_ops params tt in
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
  approx chebyshev11.
  Restart.
  approx (static 0 3,taylor).
  Restart.
  approx (chebyshev11, i_deg 15).
  Restart.
  approx (static 0.5 2, stdz60).
  Restart.
  approx (static 0.5 2, nbh IStdZ60.nbh).
  (* static (DF2 0.5%float 2%float) (i_deg 15). *)

  Restart.
  estimate (sqrt 2).
  estimate (sqrt (-2)).
  estimate (RInt (@sqrt _) 1 2) (bigint60).
  estimate (RInt (@sqrt _) 1 2) (i_deg 3, bigint120, native).
  estimate (RInt (@sqrt _) 1 2) (i_deg 3, bigint120, vm).
  estimate (RInt (@sqrt _) 1 2) (i_deg 3, primfloat, native).
  estimate (RInt (@sqrt _) 1 2) (i_deg 3, primfloat, vm).
  estimate (RInt id 0 1) (chebyshev11).
  estimate (RInt id 0 2) (static (-1) 3, taylor).
  estimate (RInt (@sqrt _) (-1) 1) (native).
Abort.
*)
