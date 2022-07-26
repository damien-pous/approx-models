(** * Examples on how to use the tactics *)

Require Import Reals Floats.
Require Import tactic.


(** the tactic [approx] solves conjunctions of inequations (<,<=,<>) 

    it supports the following operations on reals:
      +, -, *, /, sqrt, cos, abs, 0, 1, pi, fromZ, fromQ
    as well as integration of univariate functions built from
      +, -, *, /, sqrt, constant expressions as above, and the three functions id x,sin x,cos x
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

(** [approx] computes models on the encountered integral bounds
    the [static a b] option systematically uses models on [[a;b]]
 *)
Goal 0.3333 <= RInt (fun x => x*x) 0 1 <= 0.3334.
Proof.
  approx (static 0 2).
Qed.

(** Thus, when using [static], the integral bounds should lie within the given bounds *)
Goal 0 <= RInt (fun x => x*x) 0 2 <= 38.
Proof.
  Fail approx (static 0 1).
  approx (static (-1.5) 3.3).      
Abort.

Goal 1.578 <= RInt (fun x => sqrt (2+x)) 0 1 <= 1.579.
Proof.
  approx.
Qed.

(** the basis for models can be selected with [chebyshev] (default) [taylor], or [fourier]
    [taylor] does not support [sqrt] and [div] (yet)
    [fourier] does not support the identity (x), but is the only one to support [cos] and [sin]
 *)
Goal 1 <= RInt (fun x => x * (2+x)) 0 1.
Proof.
  approx taylor.
Qed.
Goal 1.5 <= RInt (fun x => sqrt (2+x)) 0 1.
Proof.
  (** error message is not clear: we lack interpolation for Taylor, so that the oracles simply do not work *)
  Fail approx taylor.
  approx.
Qed.

(** examples using Fourier basis *)
Goal 0.207 <= RInt (fun x => sin x) (pi/4) (pi/3) <= 0.208.
  Fail approx.
  approx fourier.
Qed.  
Goal 0.124 <= RInt (fun x => sin x * cos x) (pi/4) (pi/3) <= 0.126.
  approx fourier.
Qed.  
Goal 0.09 <= RInt (fun x => sin x / (2+cos x)) 0 pi <= 1.1.
  approx fourier.
Qed.  


(** [approx] also makes it possible to compare univariate functions on a given interval *)
Goal forall x, 0.1<=x<=0.9 -> x < sqrt x < sqrt (sqrt x).
  approx.
Qed.

Goal forall x, 0.1<=x<=0.9 -> x <> sqrt x.
  approx.
Qed.

(** it uses a bisection method, together with a nullability test on models requiring an oracle to estimate an inverse of the function *)
Goal forall x, 0.001<=x<=0.999 -> x <> sqrt x.
  (** recursion depth for bisection can be specified with [depth]; default is 5 *)
  Fail approx.
  approx (depth 6).
  Restart.
  (** recursion depth 1 means no bisection; in that case we need to increase the interpolation degree *)
  approx (i_deg 69, depth 1).
  Restart.
  (** a bit less with bisection depth 2 *)
  approx (i_deg 42, depth 2).
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
  approx (chebyshev11, i_deg 24). 
  Restart.
  (** with a larger static basis (chebyshev on [[-1.5;1.5]]), we need to further increase the degree *)
  approx (static (-1.5) 1.5, i_deg 41). 
Qed.

(** the interpolation degree may also by specified locally, using the [set _] identity function  *)
Goal True.
  estimate (RInt (fun x => 1/(set (degree 25) (sqrt (1+x)))) 0 1).
  estimate (RInt (fun x => 1/(set (degree 45) (sqrt (1+x)))) 0 1).
  (** similarly the [Rtruncate] identity function may be use to truncate the models obtained for certain subexpressions *)
  estimate (RInt (fun x => 1/(Rtruncate 20 (set (degree 45) (sqrt (1+x))*(1+x)))) 0 1).
  (** truncated multiplications can be specified via [Rmult'] and its infix notation [x *[deg] y] *)
  estimate (RInt (fun x => 1/(Rtruncate 20 (sqrt (1+x)) *[45] (1+x))) 0 1).
Abort.

Goal -0.1 <= RInt (fun x => x) (-2) 2 <= 0.1.
Proof.
  (* here we go beyond the default domain [[-1;1]] *)
  Fail approx chebyshev11.
  (* with a rescaled chebyshev basis *)
  approx (static (-3) 3).
Qed.

Goal 1.2189 <= RInt (fun x => sqrt (1+x)) 0 1 <= 1.219.
Proof.
  (** since we use Chebyshev basis on [[-1;1]] by default, 
     we get too close from sqrt of a negative value here *)
  Fail approx chebyshev11.
  (** solved by using a better basis *)
  approx.
Qed.

Goal 1.2189 <= RInt (fun x => sqrt (1+x)) 0 1 <= 1.219.
Proof.
  (** the vm/native options make it possible to select the evaluation strategy (vm_compute/native_compute); vm by default *)
  approx native.
  Restart.
  approx vm.
  (** the primfloat/bigint120/stdz60... options make it possible to select the floating point implementation (primitive floats, emulated floats with primitive integers or plain standard relative numbers -- at a certain precision); primfloat by default *)
  Restart.
  approx bigint120.
  Restart.
  approx (stdz60, i_deg 5).
Qed.
