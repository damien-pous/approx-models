(** * Examples on how to use the tactics *)

Require Import Reals Floats.
Require Import syntax tactic.
Require taylor chebyshev approx.


(** the tactic [dynamic] solves conjunctions of inequations (<,<=,<>) 

    it supports the following operations on reals:
      +, -, *, /, sqrt, cos, abs, 0, 1, pi, fromZ, fromQ
    as well as integration of univariate functions built from
      +, -, *, /, sqrt, and constant expressions as above
*)
Goal 1.4 <= sqrt 2 <= 1.5.
Proof.
  dynamic.
Qed.

Goal sqrt 2 < 1.5 /\ -1 <= cos pi.
Proof.
  dynamic.
Qed.

Goal 0.3333 <= RInt (fun x => x*x) 0 1 <= 0.3334.
Proof.
  dynamic.
Qed.

(** [dynamic] computes models, using Chebyshev basis rescaled to the encountered integral bounds
    the [static11] variant systematically uses Chebyshev basis on [-1;1]
 *)
Goal 0.3333 <= RInt (fun x => x*x) 0 1 <= 0.3334.
Proof.
  static11.
Qed.

(** Thus, the integral bounds should lie within [-1;1] in this case 
    or we can use the [static] variant, which uses Chebyshev basis on the given domain
 *)
Goal 0 <= RInt (fun x => x*x) 0 2 <= 38.
Proof.
  Fail static11.
  static (DQ2 (-1.5) 3.3).      
Abort.

Lemma ex7: 1.578 <= RInt (fun x => sqrt (2+x)) 0 1 <= 1.579.
Proof.
  dynamic.
Qed.


(** the tactic [dynamic_est e] makes it possible to compute and print an interval enclosing the expression [e]
    this would typically be the estimation used by the [dynamic] tactic.
 *)
Goal True.
Proof.
  dynamic_est (RInt (fun x => x*x) 0 1).
  dynamic_est (RInt (fun x => x/(sqrt (1+x))) 0 1).
Abort.

(** a first argument may be passed to [dynamic/dynamic_est] in order to specify
    the interpolation degree used to compute models for divisions and square roots *)
Lemma ex2: 0.405465108108 <= RInt (fun x => 1/(2+x)) 0 1 <= 0.405465108109.
  (** ln3 - ln2 = 0.405465108108 *)
  Fail dynamic.
  dynamic_est (RInt (fun x => 1/(2+x)) 0 1). 
  dynamic_est 13%Z (RInt (fun x => 1/(2+x)) 0 1). 
  (** need to increase the interpolation degree *)
  dynamic 13%Z.
  Restart.
  (** with a static basis (chebyshev on [-1;1]), we need to further increase the degree *)
  static11 23%Z. 
  Restart.
  (** with a larger static basis (chebyshev on [-1.5;1.5]), we need to further increase the degree *)
  static (DQ2 (-1.5) 1.5) 40%Z. 
Qed.

Lemma ex5: -0.1 <= RInt (fun x => x) (-2) 2 <= 0.1.
Proof.
  (* here we go beyond the default domain [-1;1] *)
  Fail static11.
  (* with a rescaled chebyshev basis *)
  static (DZ2 (-3) 3).
  Restart.
  (* with the monomial basis *)
  gen_check (Static.check (taylor_model (DZ2 (-2) 2))) 5%Z.
Qed.

Lemma ex7': 1.2189 <= RInt (fun x => sqrt (1+x)) 0 1 <= 1.219.
Proof.
  (** since we use Chebyshev basis on [-1;1] by default, 
     we get too close from sqrt of a negative value here *)
  Fail static11.
  (** solved by using a better basis *)
  dynamic.
Qed.
