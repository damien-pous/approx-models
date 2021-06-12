(** * tests for the library *)

Require Import intervals rescale errors tactic syntax.
Require taylor chebyshev approx.

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
  approx (i_static 0.5 2).
  Restart.
  approx (i_static 0.5 2, i_deg 15).
Qed.

Goal 1.5 <= sqrt 2 <= 1.6.
Proof.
  Fail approx.
Abort.

Goal 1 <= 2.
Proof. approx. Qed.
Goal 1 < 2.
Proof. approx. Qed.
Goal 2 > 1.
Proof. approx. Qed.
Goal 2 >= 1.
Proof. approx. Qed.

Lemma ex1: 0.3333 <= RInt (fun x => x*x) 0 1 <= 0.3334.
Proof.
  approx.
Qed.

Lemma ex2: 0.9999 <= RInt (fun x => x*x*3.0) 0 1 <= 1.00001.
Proof.
  approx.
Qed.

Lemma ex4: 2.08670 <= RInt (fun x => (1+x)/((1-x)*(1-x)+1/4)) 0 (pi/4)  <= 2.08672.
  approx (i_deg 11).
Abort.

Lemma ex5: -0.1 <= RInt (fun x => x) (-2) 2 <= 0.1.
Proof.
  (* here we go beyond the default domain [-1;1] *)
  Fail approx (i_static11).
  (* with a rescaled chebyshev basis *)
  approx (i_deg 5).
Qed.

Lemma ex5': 0 <= RInt (fun x => x) (-2) 2 <= 0.
Proof.
  (* we cannot be that precise! *)
  Fail approx (i_deg 5).
Abort.

Lemma ex6: -0.1 <= RInt (fun x => 0%R) (-1/3) (1/3) <= 0.1.
Proof.
  approx.
Qed.

Lemma ex6': -0.1 <= RInt (fun x => 0%R) (-3) (3) <= 0.1.
Proof.
  Fail approx (i_static11).
  approx. 
Qed.

Goal RInt (fun x => RInt id 1 x) 0 1 <= 5.
  Fail approx.
Abort.

Goal forall x, 0<=x<=1 -> 1<2.
  approx.
Qed.
Goal forall x, 0<=x<=1 -> x<2.
  approx.
Qed.
Goal forall x, 0.1<=x<=0.9 -> x*x<x.
  approx.
Qed.
Goal forall x, 0.1<=x<=0.9 -> x < sqrt x.
  approx.
Qed.
Goal forall x, 0.1<=x<=0.9 -> x <> sqrt x.
  approx.
Qed.


(** direct computations  *)
(* Need to reenable notations for syntactic expressions first *)
Eval vm_compute in
    let e := EXPR ((integrate' (1 / (1 + id'))) 0 (pi'/fromZ' 4)) in 
    LET E ::= Dynamic.Sem' chebyshev_model_ops 20 e IN ret (width E).

Eval vm_compute in
    let e := EXPR (integrate' ((1+id') / ((1-id')*(1-id')+1/fromZ' 4)) 0 (pi'/fromZ' 4)) in
    LET E ::= Static.Sem' chebyshev11_model_ops 20 e IN ret (width E).
    (** increase 20 to get more digits *)


(** testing interpolation on rescaled bases *)
Eval vm_compute in
    let f := FXPR (id' / fsqrt ((1+id') / (fromZ' 3+id'))) in
    Static.Sem' (chebyshev_model_ops (fromZ 18) (fromZ 200)) 10 f.


(** Note that the neighborhood is set by default to [Iprimitive.nbh], i.e., intervals with primitive floating point endpoints 
   other candidates include:
   - [IBigInt.nbh]: intervals with floating points endpoints, floating points being represented via primitive 63bit integers (less axioms, a bit less efficient)
   - [IZ.nbh]: intervals with floating points endpoints, floating points being represented via Coq integers (Z) (no axioms, not so efficient)
  *)

Eval vm_compute in
    let e := EXPR (integrate' ((1+id') / ((1-id')*(1-id')+1/fromZ' 4)) 0 (pi'/fromZ' 4)) in
    e_map width (Static.Sem' (N:=IZ53.nbh) chebyshev11_model_ops 10 e).
(* above: need 1sec *)
(* below: also need 1sec thanks to sharing *)
Eval vm_compute in
    let e := EXPR (let_ee x := integrate' ((1+id') / ((1-id')*(1-id')+1/fromZ' 4)) 0 (pi'/fromZ' 4)
                       in x + x)
    in
    e_map width (Static.Sem' (N:=IZ53.nbh) chebyshev11_model_ops 10 e).

Time Eval vm_compute in
    let e := FXPR ((1+id') / ((1-id')*(1-id')+1/fromZ' 4)) in
    Static.Sem' (N:=IZ53.nbh) chebyshev11_model_ops 12 e.
(* above: need 1sec *)
(* below: also need 1sec thanks to sharing *)
Time Eval vm_compute in
    let e := FXPR (let_ff x := (1+id') / ((1-id')*(1-id')+1/fromZ' 4)
                       in x + x)
    in
    Static.Sem' (N:=IZ53.nbh) chebyshev11_model_ops 12 e.



(* TOCHECK: why is 1+1 not a singleton with primitive floats? *)
Eval vm_compute in (fromZ 2: Ifloat53.nbh).
Eval vm_compute in (1-1: Ifloat53.nbh).     (* arg *)
Eval vm_compute in (1+1: Ifloat53.nbh).     (* arg *)
Eval vm_compute in (1+1: IZ53.nbh).         (* ok *)
Eval vm_compute in (1+1: IBigInt53.nbh).    (* ok *)


(** About neighborhood instances: *)
(*
Print Assumptions syntax.Dynamic.check.   (** only three axioms for the (classical) construction of reals *)
Print Assumptions approx.model.           (** plus excluded middle for classical logic *)
Print Assumptions chebyshev.basis.        (** idem *)
Print Assumptions IZ.nbh.                 (** idem, everything is emulated *)
Print Assumptions IBigInt.nbh.            (** plus axioms for primitive 63bits integers (Int63) *)
Print Assumptions Iprimitive.nbh.         (** plus axioms for primitive floats (PrimFloat) *)
*)
