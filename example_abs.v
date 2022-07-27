(** * Example 1: on approximations of the absolute value function *)

Require Import Reals.
Require Import Coquelicot.Coquelicot.
Open Scope R_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** the following function approximates the absolute value function on reals:
    the smaller [eps], the closer [g eps] from [abs] 
    below ve verify some properties of this function
 *)
Definition g eps x := sqrt (eps*eps + x*x).


(** ** with CoqApprox.interval  *)
From Interval Require Import Tactic.

Goal let eps := 1/10 in
     forall x, 0 <= x <= 1 -> g eps x - x < eps+eps/10.
Proof.
  intros eps x H; unfold eps, g.
  (** does not work with Taylor models *)
  Fail interval with (i_taylor x).
  (** even with large degrees (and degrees around 100-200 are really slow to compute)*)
  Fail interval with (i_taylor x, i_degree 50).
  (* Fail interval with (i_taylor x, i_degree 100). *)

  (** works easily with subdivision *)
  interval with (i_bisect x).
Qed.

Goal let eps := 1/100 in
     forall x, 0 <= x <= 1 -> g eps x - x < eps+eps/10.
Proof.
  intros eps x H; unfold eps, g.
  interval with (i_bisect x).
Qed.

Goal let eps := 1/1000 in
     forall x, 0 <= x <= 1 -> g eps x - x < eps+eps/10.
Proof.
  intros eps x H; unfold eps, g.
  interval with (i_bisect x).
Qed.

(** we also need subdivision to approximate related integrals: 
    Taylor models, even with a high degree, are not precise enough *)
Goal let eps := 1/10 in 1/2+eps/10 <= RInt (g eps) 0 1 <= 1/2+eps+eps/10.
  intro eps. unfold g, eps.
  (** [i_fuel 1] means no subdivision *)
  Fail integral with (i_fuel 1).
  (** larger degrees for Taylor models are expensive, and to not permit to conclude  *)
  Fail integral with (i_fuel 1, i_degree 20).
  (* Fail integral with (i_fuel 1, i_degree 60, i_prec 300). *)
  (** works with subdivision *)
  integral with (i_fuel 3).     
Qed.

Goal let eps := 1/1000 in 1/2+eps/1000 <= RInt (g eps) 0 1 <= 1/2+eps+eps/10.
  intro eps. unfold g, eps.
  (** works with more subdivision *)
  integral with (i_fuel 13).     
Qed.

(** ** with Chebyshev models (present library) *)
Require Import approx rescale intervals syntax tactic.
Require chebyshev.

Goal let eps := 1/10 in
     forall x, 0 <= x <= 1 -> g eps x - x < eps+eps/10.
Proof.
  intros eps; unfold eps, g.
  approx (i_deg 11).
Qed.

(* since we construct a single Chebyshev model, integration works smoothly, without subdivision *)
Goal let eps := 1/10 in 1/2+eps/10 <= RInt (g eps) 0 1 <= 1/2+eps+eps/10.
  intro eps. unfold g, eps.
  approx. 
Qed.

Goal let eps := 1/100 in
     forall x, 0 <= x <= 1 -> g eps x - x < eps+eps/10.
Proof.
  intros eps; unfold eps, g.
  (** default degree (10) does not make it possible to construct a model for the square root  *)
  Fail approx (depth 1).
  (** degree 15 makes it possible to construct a model, but this model is not precise enough *)
  Fail approx (i_deg 15, depth 1).
  (** at degree 35, we get a proof *)
  approx (i_deg 35, depth 1). 
  (** or just 32 if we do not truncate *)
  Restart. intros eps; unfold eps, g.
  approx (i_deg (-32), depth 1).
  (** alternatively, we get a proof at degree 10 if we do not forbid bisection (by not specifying [depth 1]) *)
  Restart.
  intros eps; unfold eps, g.
  approx. 
Qed.

Goal let eps := 1/100 in 1/2+eps/100 <= RInt (g eps) 0 1 <= 1/2+eps+eps/10.
  intro eps. unfold g, eps.
  approx (i_deg 32). 
Qed.

(** for smaller values of epsilon, we need more precision for the floating points themselves *)
Goal let eps := 1/1000 in
     forall x, 0 <= x <= 1 -> g eps x - x < eps+eps/10.
Proof.
  intros eps; unfold eps, g.
  (** model constructed at degree 81, but not precise enough *)
  Fail approx (i_deg 81, depth 1).
  (** and not precise enough, even with pretty big degrees (e.g., 500) *)
  (* Fail approx (i_deg 300).            *)
  (* Fail approx (i_deg 400).            *)
  (* Fail approx (i_deg 500).            *)
  (** at degree 102 we get a proof when using a higher precision *)
  (* Time approx (i_deg 102, depth 1, bigint300, native). (* 15s *) *)
  
  (** subdivision works nicely, and much faster... *)
  approx (depth 8). 
Qed.


(** ** direct computations *)

(** two domains: [[-1;0]] and [[0;1]]  *)
Definition D10: Domain := DZ2 (-1) 0.
Definition D01: Domain := DZ2 0 1.

(** associated model operations, plus operations on [[-1;1]]
    note the implicit use of [Iprimitive.nbh] *)
Definition F11 := approx.model_ops chebyshev.basis11_ops.
Definition F10 := approx.model_ops (chebyshev.basis_ops (fromZ (-1)) 0).
Definition F01 := approx.model_ops (chebyshev.basis_ops 0            1).

(** width of the remainder of a model *)
Definition wrem (x: E (Tube II)) := x >>= fun x => ret (width (rem x)). 

(** model approximating the absolute value function,
    parameterised by 
    - [deg]: the interpolation degree for square root
    - [None]: no truncation in validation
    - [eps]: the smaller the better *)
Definition NearAbs (MM: ModelOps) (deg: Z) (eps: Q): E MM :=
  elet mid := mid in
  msqrt deg None (mcst (fromQ (eps*eps)) + mid * mid). 



(** below we compute rigorous approximations over [[-1;1]] or [[0;1]], and we check their remainders.
    it is always much easier to get approximations on [[0;1]] *)

(** eps = 1/10 *)
Eval native_compute in (wrem (NearAbs F11  10 0.1)).
Eval native_compute in (wrem (NearAbs F11  20 0.1)).
Eval native_compute in (wrem (NearAbs F11  30 0.1)).
Eval native_compute in (wrem (NearAbs F11  40 0.1)).
Eval native_compute in (wrem (NearAbs F11  50 0.1)). (* 0.0001 *)
Eval native_compute in (wrem (NearAbs F11  60 0.1)).
Eval native_compute in (wrem (NearAbs F11  70 0.1)).
Eval native_compute in (wrem (NearAbs F11  80 0.1)).
Eval native_compute in (wrem (NearAbs F11  90 0.1)). (* 2e-6 *)
Eval native_compute in (wrem (NearAbs F11 100 0.1)). (* 4e-7  *)
(* easier on [[0;1]] *)
Eval native_compute in (wrem (NearAbs F01  50 0.1)). (* 7e-13 *)

(** eps^2 ~ 1/1000 *)
Eval native_compute in (wrem (NearAbs F11  10 0.032)). (* err *)
Eval native_compute in (wrem (NearAbs F11  20 0.032)). (* err *)
Eval native_compute in (wrem (NearAbs F11  30 0.032)). (* err *)
Eval native_compute in (wrem (NearAbs F11  35 0.032)). (* 0.02 *)
Eval native_compute in (wrem (NearAbs F11  40 0.032)). (* err *)
Eval native_compute in (wrem (NearAbs F11  50 0.032)). (* err *)
Eval native_compute in (wrem (NearAbs F11  60 0.032)). (* 0.011  *)
Eval native_compute in (wrem (NearAbs F11  70 0.032)). (* 0.004  *)
Eval native_compute in (wrem (NearAbs F11  80 0.032)). (* 0.002  *)
Eval native_compute in (wrem (NearAbs F11  90 0.032)). (* 0.001  *)
Eval native_compute in (wrem (NearAbs F11 100 0.032)). (* 0.0007 *)
(* easier on [[0;1]] *)
Eval native_compute in (wrem (NearAbs F01  20 0.032)). (* 9e-5 *)

(** eps = 1/100 *)
Eval native_compute in (wrem (NearAbs F11 100 0.01)). (* err *)
Eval native_compute in (wrem (NearAbs F11 200 0.01)). (* 0.004 *)
(** above: this means we could use (NearAbs F11 200 0.01) as a 
    model for the absolute value function on [[-1;1]], 
    with error around 0.004+0.01=0.014 *)
(* easier on [[0;1]] *)
Eval native_compute in (wrem (NearAbs F01  50 0.01)). (* 2e-6 *)
Eval native_compute in (wrem (NearAbs F01 100 0.01)). (* 7e-10 *)

(** eps = 1/1000 *)
Eval native_compute in (wrem (NearAbs F11 100 0.001)). (* err *)
Eval native_compute in (wrem (NearAbs F11 500 0.001)). (* not even with degree 1000 *)
(* easier on [[0;1]] *)
Eval native_compute in (wrem (NearAbs F01  81 0.001)). (* 7e-5 *)



(** ** comparing timings for constructing models *)
(** Chebyshev models on [[-1;1]], with a posteriori validation for square root *)
Time Eval native_compute in (wrem (NearAbs F11  10 2)).
Time Eval native_compute in (wrem (NearAbs F11  10 2)).
Time Eval native_compute in (wrem (NearAbs F11  20 2)).
Time Eval native_compute in (wrem (NearAbs F11  30 2)). (* maximal precision already obtained here *)
Time Eval native_compute in (wrem (NearAbs F11  40 2)).
Time Eval native_compute in (wrem (NearAbs F11  50 2)).
Time Eval native_compute in (wrem (NearAbs F11  60 2)).
Time Eval native_compute in (wrem (NearAbs F11  70 2)).
(* Time Eval native_compute in (wrem (NearAbs F11  80 2)). *)
(* Time Eval native_compute in (wrem (NearAbs F11  90 2)). *)
(* Time Eval native_compute in (wrem (NearAbs F11 100 2)). *)
(* Time Eval native_compute in (wrem (NearAbs F11 110 2)). *)
(* Time Eval native_compute in (wrem (NearAbs F11 120 2)). *)
(* Time Eval native_compute in (wrem (NearAbs F11 130 2)). *)
(* Time Eval native_compute in (wrem (NearAbs F11 140 2)). *)
(* Time Eval native_compute in (wrem (NearAbs F11 150 2)). *)
(* Time Eval native_compute in (wrem (NearAbs F11 160 2)). *)
(* Time Eval native_compute in (wrem (NearAbs F11 170 2)). *)
(* Time Eval native_compute in (wrem (NearAbs F11 180 2)). *)
(* Time Eval native_compute in (wrem (NearAbs F11 190 2)). *)
(* Time Eval native_compute in (wrem (NearAbs F11 200 2)). *)

(** Taylor models, with CoqApprox.interval *)
Goal forall x, -1 <= x <= 1 -> R_sqrt.sqrt (2 + x^2) <= 0.
Proof.
  intros.
  (* ignore the first one with native_compute, which needs to be initialised *)
  Time Fail interval with (i_native_compute, i_taylor x, i_degree  10).
  Time Fail interval with (i_native_compute, i_taylor x, i_degree  10).
  Time Fail interval with (i_native_compute, i_taylor x, i_degree  20).
  Time Fail interval with (i_native_compute, i_taylor x, i_degree  30).
  Time Fail interval with (i_native_compute, i_taylor x, i_degree  40).
  Time Fail interval with (i_native_compute, i_taylor x, i_degree  50).
  Time Fail interval with (i_native_compute, i_taylor x, i_degree  60).
  Time Fail interval with (i_native_compute, i_taylor x, i_degree  70).
  (*
  Time Fail interval with (i_native_compute, i_taylor x, i_degree  80).
  Time Fail interval with (i_native_compute, i_taylor x, i_degree  90).
  Time Fail interval with (i_native_compute, i_taylor x, i_degree 100).
  Time Fail interval with (i_native_compute, i_taylor x, i_degree 110).
  Time Fail interval with (i_native_compute, i_taylor x, i_degree 120).
  Time Fail interval with (i_native_compute, i_taylor x, i_degree 130).
  Time Fail interval with (i_native_compute, i_taylor x, i_degree 140).
  Time Fail interval with (i_native_compute, i_taylor x, i_degree 150).
  Time Fail interval with (i_native_compute, i_taylor x, i_degree 160).
  Time Fail interval with (i_native_compute, i_taylor x, i_degree 170).
  Time Fail interval with (i_native_compute, i_taylor x, i_degree 180).
  Time Fail interval with (i_native_compute, i_taylor x, i_degree 190).
  Time Fail interval with (i_native_compute, i_taylor x, i_degree 200).
   *)
Abort.


(** ** computing the error between [NearAbs deg eps] and [abs] on [[0;1]], directly *)
Definition NearAbsErr01 (deg : Z) (eps: Q) :=
  elet mid := mid in
  elet G := @NearAbs F01 deg eps in
  ret (width (mrange (G - mid))).

Eval vm_compute in (NearAbsErr01 10 0.1). (* 0.16 *)
Eval vm_compute in (NearAbsErr01 30 0.1). (* 0.16 *)
Eval vm_compute in (NearAbsErr01 60 0.1). (* 0.16 *)

Eval vm_compute in (NearAbsErr01 10 0.032). (* 0.07 *)
Eval vm_compute in (NearAbsErr01 30 0.032). (* 0.06 *)
Eval vm_compute in (NearAbsErr01 60 0.032). (* 0.06 *)

Eval vm_compute in (NearAbsErr01 10 0.01). (* err *)
Eval vm_compute in (NearAbsErr01 30 0.01). (* 0.02 *)
Eval vm_compute in (NearAbsErr01 60 0.01). (* 0.02 *)

Eval vm_compute in (NearAbsErr01  50 0.001).  (* err *)
Eval vm_compute in (NearAbsErr01 100 0.001).  (* 0.002 *)
Eval vm_compute in (NearAbsErr01 200 0.001).  (* 0.002 *)
