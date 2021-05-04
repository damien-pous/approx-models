(** * tests for the library *)

Require Import intervals rescale errors tactic syntax.
Require taylor chebyshev approx.

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

Goal 1.5 <= sqrt 2 <= 1.6.
Proof.
  Fail dynamic (sqrt (fromZ 2)).
Abort.

Lemma ex1: 0.3333 <= RInt (fun x => x*x) 0 1 <= 0.3334.
Proof.
  dynamic (e_integrate (f_id * f_id) 0 1).
Qed.

Lemma ex4: 2.08670 <= RInt (fun x => (1+x)/((1-x)*(1-x)+1/4)) 0 (pi/4)  <= 2.08672.
  dynamic (e_integrate ((1+f_id) / ((1-f_id)*(1-f_id)+1/fromZ 4)) 0 (pi/fromZ 4)) 11%Z.
Abort.

Lemma ex5: -0.1 <= RInt (fun x => x) (-2) 2 <= 0.1.
Proof.
  (* here we go beyond the default domain [-1;1] *)
  Fail static11 (e_integrate f_id (fromZ (-2)) (fromZ 2)).
  (* with a rescaled chebyshev basis *)
  dynamic (e_integrate f_id (fromZ (-2)) (fromZ 2)) 5%Z.
Qed.

Lemma ex5': 0 <= RInt (fun x => x) (-2) 2 <= 0.
Proof.
  (* we cannot be that precise! *)
  Fail dynamic (e_integrate f_id (fromZ (-2)) (fromZ 2)) 5%Z.
Abort.

Lemma ex6: -0.1 <= RInt (fun x => 0%R) (-1/3) (1/3) <= 0.1.
Proof.
  dynamic (e_integrate f_zer (fromZ (-1)/fromZ 3) (fromZ 1/fromZ 3)).
Qed.

Lemma ex6': -0.1 <= RInt (fun x => 0%R) (-3) (3) <= 0.1.
Proof.
  Fail static11 (e_integrate f_zer (fromZ (-3)) (fromZ 3)).
  dynamic (e_integrate f_zer (fromZ (-3)) (fromZ 3)). 
Qed.

(** direct computations  *)

Eval vm_compute in
    let e := (e_integrate ((1+f_id) / ((1-f_id)*(1-f_id)+1/fromZ 4)) 0 (pi/fromZ 4)) in
    LET E ::= Static.eSem chebyshev11_model_ops 20 e IN ret (width E).
    (** increase 20 to get more digits *)


(** testing interpolation on rescaled bases *)
Eval vm_compute in
    let f: fxpr := f_id / sqrt ((1+f_id) / (fromZ 3+f_id)) in
    Static.fSem (chebyshev_model_ops (fromZ 18) (fromZ 200)) 10 f.


(** Note that the neighborhood is set by default to [Iprimitive.nbh], i.e., intervals with primitive floating point endpoints 
   other candidates include:
   - [IBigInt.nbh]: intervals with floating points endpoints, floating points being represented via primitive 63bit integers (less axioms, a bit less efficient)
   - [IZ.nbh]: intervals with floating points endpoints, floating points being represented via Coq integers (Z) (no axioms, not so efficient)
  *)

Eval vm_compute in
    let e := (e_integrate ((1+f_id) / ((1-f_id)*(1-f_id)+1/fromZ 4)) 0 (pi/fromZ 4)) in
    e_map width (Static.eSem (N:=IZ.nbh) chebyshev11_model_ops 20 e).


(* TOCHECK: why is 1+1 not a singleton with primitive floats? *)
Eval vm_compute in (fromZ 2: Iprimitive.nbh).
Eval vm_compute in (1+1: Iprimitive.nbh). (* arg *)
Eval vm_compute in (1+1: IZ.nbh).         (* ok *)
Eval vm_compute in (1+1: IBigInt.nbh).    (* ok *)


(** About neighborhood instances:
Print Assumptions syntax.bound.   (** only four axioms for the (classical) construction of reals *)
Print Assumptions approx.model.   (** idem *)
Print Assumptions chebyshev.basis.(** idem *)
Print Assumptions IZ.nbh.         (** idem, only 4, everything is emulated *)
Print Assumptions IBigInt.nbh.    (** plus axioms for primitive 63bits integers (Int63) *)
Print Assumptions Iprimitive.nbh. (** plus axioms for primitive floats (PrimFloat) *)
 *)
