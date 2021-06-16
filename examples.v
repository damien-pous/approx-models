(** * Examples on how to use the tactics *)

Require Import Reals Floats.
Require Import syntax tactic intervals.
Require taylor chebyshev approx.


(** the tactic [approx] solves conjunctions of inequations (<,<=,<>) 

    it supports the following operations on reals:
      +, -, *, /, sqrt, cos, abs, 0, 1, pi, fromZ, fromQ
    as well as integration of univariate functions built from
      +, -, *, /, sqrt, and constant expressions as above
*)
Goal 1.4 <= sqrt 2 <= 1.5.
Proof.
  approx.
Qed.

Goal sqrt 2 < 1.5 /\ -1 <= cos pi.
Proof.
  approx.
Qed.

Goal 0.3333 <= RInt (fun x => x*x) 0 1 <= 0.3334.
Proof.
  approx.
Qed.

(** [approx] computes models, using Chebyshev basis rescaled to the encountered integral bounds
    the [static11] option systematically uses Chebyshev basis on [[-1;1]]
 *)
Goal 0.3333 <= RInt (fun x => x*x) 0 1 <= 0.3334.
Proof.
  approx static11.
Qed.

(** Thus, the integral bounds should lie within [[-1;1]] in this case 
    or we can use the [static] option, which uses Chebyshev basis on the given domain
 *)
Goal 0 <= RInt (fun x => x*x) 0 2 <= 38.
Proof.
  Fail approx static11.
  approx (static (-1.5) 3.3).      
Abort.

Goal 1.578 <= RInt (fun x => sqrt (2+x)) 0 1 <= 1.579.
Proof.
  approx.
Qed.

(** [approx] also makes it possible to compare univariate functions on a given interval
    (the goal show be presented in a rather strict way for now, essentially as in the two examples below; this should be improved in the following release)
 *)
Goal forall x, 0.1<=x<=0.9 -> x < sqrt x.
  approx.
Qed.

Goal forall x, 0.1<=x<=0.9 -> x <> sqrt x.
  approx.
Qed.



(** the tactic [estimate e] makes it possible to compute and print an interval enclosing the expression [e]
    this would typically be the estimation used by the [approx] tactic.
 *)
Goal True.
Proof.
  estimate (RInt (fun x => x*x) 0 1).
  estimate (RInt (fun x => x/(sqrt (1+x))) 0 1).
  estimate (RInt (fun x => x/(sqrt (1+x))) 0 1) (static 0 3).
Abort.

(** the [i_deg] option makes it possible to specify
    the interpolation degree used to compute models for divisions and square roots *)
Goal 0.405465108108 <= RInt (fun x => 1/(2+x)) 0 1 <= 0.405465108109.
  (** ln3 - ln2 = 0.405465108108 *)
  Fail approx.
  estimate (RInt (fun x => 1/(2+x)) 0 1). 
  estimate (RInt (fun x => 1/(2+x)) 0 1) (i_deg 13). 
  (** need to increase the interpolation degree *)
  approx (i_deg 13).
  Restart.
  (** with a static basis (chebyshev on [[-1;1]]), we need to further increase the degree *)
  approx (static11, i_deg 23). 
  Restart.
  (** with a larger static basis (chebyshev on [[-1.5;1.5]]), we need to further increase the degree *)
  approx (static (-1.5) 1.5, i_deg 40). 
Qed.

Goal -0.1 <= RInt (fun x => x) (-2) 2 <= 0.1.
Proof.
  (* here we go beyond the default domain [[-1;1]] *)
  Fail approx (static11).
  (* with a rescaled chebyshev basis *)
  approx (static (-3) 3).
Qed.

Goal 1.2189 <= RInt (fun x => sqrt (1+x)) 0 1 <= 1.219.
Proof.
  (** since we use Chebyshev basis on [[-1;1]] by default, 
     we get too close from sqrt of a negative value here *)
  Fail approx (static11).
  (** solved by using a better basis *)
  approx.
Qed.

Goal 1.2189 <= RInt (fun x => sqrt (1+x)) 0 1 <= 1.219.
Proof.
  (** the vm/native options make it possible to select the evaluation strategy (vm_compute/native_compute); vm by default *)
  approx native.
  Restart.
  approx vm.
  (** the primfloat/bigint120/stdz60... options make it possible to select the floating point implementation (primitive floats, emulated floats with primitive integers or plain stanard relative numbers -- at a certain precision); primfloat by default *)
  Restart.
  approx bigint120.
  Restart.
  approx (stdz60, i_deg 5).
Qed.
