(** Example 1: rigorous approximations of the absolute value function *)

(* DAMIEN to FLORENT : I inserted a few 'TOCHECK' for you... *)

Require Import Reals.
Open Scope R_scope.


(** * with CoqApprox.interval  *)
From Interval Require Import Tactic.
Definition f1 eps x := sqrt (eps^2 + x^2).

Fact test0 x :
  let eps := 1/1000 in
  -1 <= x <= 1 ->
  Rabs (f1 eps x - Rabs x) <= eps+1/10000.
Proof.
  intros eps H; subst eps; unfold f1.
  (** does not work without subdivision *)
  Fail interval.
  (** works with *)
  interval with (i_bisect x).
Qed.

Fact test1 x :
  let eps := 1/1000 in
  0 <= x <= 1 ->
  Rabs (f1 eps x - x) <= eps+1/10000.
Proof.
  intros eps H; subst eps; unfold f1.
  (** does not work without subdivision *)
  Fail interval.
  (** works with *)
  interval with (i_bisect x).
Qed.


(** * with our library *)
Require Import approx rescale intervals errors.
Require chebyshev.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** two domains: [-1;0] and [0;1]  *)
Definition D10: Domain := DZ2 (-1) 0.
Definition D01: Domain := DZ2 0 1.

(** associated model operations, plus operations on [-1;1]
    note the implicit use of [Iprimitive.nbh] *)
Definition F11 := approx.model_ops chebyshev.basis11_ops.
Definition F10 := approx.model_ops (chebyshev.basis_ops (fromZ (-1)) 0).
Definition F01 := approx.model_ops (chebyshev.basis_ops 0            1).

(** width of the remainder of a model *)
Definition wrem (x: E (Tube II)) := x >>= fun x => ret (width (rem x)). 

(** model approximating the absolute value function,
    parameterised by 
    - [deg]: the interpolation degree for square root
    - [eps]: the smaller the better *)
Definition NearAbs (MM: ModelOps) (deg: Z) (eps: Q): E MM := msqrt deg (mcst (fromQ eps) + mid * mid). 



(** First, compute rigorous approximations over [-1,1] and check remainders *)

(** eps = 1/10 *)
Time Eval native_compute in (wrem (NearAbs F11  10 0.1)).
Time Eval native_compute in (wrem (NearAbs F11  20 0.1)).
Time Eval native_compute in (wrem (NearAbs F11  30 0.1)).
Time Eval native_compute in (wrem (NearAbs F11  40 0.1)).
Time Eval native_compute in (wrem (NearAbs F11  50 0.1)).
Time Eval native_compute in (wrem (NearAbs F11  60 0.1)).
Time Eval native_compute in (wrem (NearAbs F11  70 0.1)).
Time Eval native_compute in (wrem (NearAbs F11  80 0.1)).
Time Eval native_compute in (wrem (NearAbs F11  90 0.1)).
Time Eval native_compute in (wrem (NearAbs F11 100 0.1)).

(** eps = 1/100 *)
Time Eval native_compute in (wrem (NearAbs F11  10 0.01)).
Time Eval native_compute in (wrem (NearAbs F11  20 0.01)).
Time Eval native_compute in (wrem (NearAbs F11  30 0.01)).
Time Eval native_compute in (wrem (NearAbs F11  40 0.01)).
Time Eval native_compute in (wrem (NearAbs F11  50 0.01)).
Time Eval native_compute in (wrem (NearAbs F11  60 0.01)).
Time Eval native_compute in (wrem (NearAbs F11  70 0.01)).
Time Eval native_compute in (wrem (NearAbs F11  80 0.01)).
Time Eval native_compute in (wrem (NearAbs F11  90 0.01)).
Time Eval native_compute in (wrem (NearAbs F11 100 0.01)).

(** eps = 1/1000 *)
(* TOCHECK: we only get one non-error value *)
Time Eval native_compute in (wrem (NearAbs F11  10 0.001)).
Time Eval native_compute in (wrem (NearAbs F11  20 0.001)).
Time Eval native_compute in (wrem (NearAbs F11  30 0.001)).
Time Eval native_compute in (wrem (NearAbs F11  35 0.001)). (* yep *)
Time Eval native_compute in (wrem (NearAbs F11  40 0.001)).
Time Eval native_compute in (wrem (NearAbs F11  50 0.001)).
Time Eval native_compute in (wrem (NearAbs F11  60 0.001)).
Time Eval native_compute in (wrem (NearAbs F11  70 0.001)).
Time Eval native_compute in (wrem (NearAbs F11  80 0.001)).
Time Eval native_compute in (wrem (NearAbs F11  90 0.001)).
Time Eval native_compute in (wrem (NearAbs F11 100 0.001)).

(** eps = 1/10000 *)
(* TOCHECK: we only get errors *)
Time Eval native_compute in (wrem (NearAbs F11  10 0.0001)).
Time Eval native_compute in (wrem (NearAbs F11  20 0.0001)).
Time Eval native_compute in (wrem (NearAbs F11  30 0.0001)).
Time Eval native_compute in (wrem (NearAbs F11  40 0.0001)).
Time Eval native_compute in (wrem (NearAbs F11  50 0.0001)).
Time Eval native_compute in (wrem (NearAbs F11  60 0.0001)).
Time Eval native_compute in (wrem (NearAbs F11  70 0.0001)).
Time Eval native_compute in (wrem (NearAbs F11  80 0.0001)).
Time Eval native_compute in (wrem (NearAbs F11  90 0.0001)).
Time Eval native_compute in (wrem (NearAbs F11 100 0.0001)).
Time Eval native_compute in (wrem (NearAbs F11 200 0.0001)).

(** compare timings with coqapprox, with eps=2 *)
Time Eval native_compute in (wrem (NearAbs F11  10 2)).
Time Eval native_compute in (wrem (NearAbs F11  10 2)).
Time Eval native_compute in (wrem (NearAbs F11  20 2)).
Time Eval native_compute in (wrem (NearAbs F11  30 2)).
Time Eval native_compute in (wrem (NearAbs F11  40 2)).
Time Eval native_compute in (wrem (NearAbs F11  50 2)).
Time Eval native_compute in (wrem (NearAbs F11  60 2)).
Time Eval native_compute in (wrem (NearAbs F11  70 2)).
Time Eval native_compute in (wrem (NearAbs F11  80 2)).
Time Eval native_compute in (wrem (NearAbs F11  90 2)).
Time Eval native_compute in (wrem (NearAbs F11 100 2)).
Time Eval native_compute in (wrem (NearAbs F11 110 2)).
Time Eval native_compute in (wrem (NearAbs F11 120 2)).
Time Eval native_compute in (wrem (NearAbs F11 130 2)).
Time Eval native_compute in (wrem (NearAbs F11 140 2)).
Time Eval native_compute in (wrem (NearAbs F11 150 2)).
Time Eval native_compute in (wrem (NearAbs F11 160 2)).
Time Eval native_compute in (wrem (NearAbs F11 170 2)).
Time Eval native_compute in (wrem (NearAbs F11 180 2)).
Time Eval native_compute in (wrem (NearAbs F11 190 2)).
Time Eval native_compute in (wrem (NearAbs F11 200 2)).

(* TOCHECK: coqapprox no longer fails! *)
Fact coqapprox_no_longer_fails (x : R) : 0 <= x <= 1 -> R_sqrt.sqrt (1/100 + x^2) <= 200.
Proof.
   intros.
   (* i_bisect_taylor doesn't seem to be available anymore, but i_bisect does the job! *)
   interval with (i_depth 1, i_bisect x, i_prec 64).
Qed.

(* TOCHECK: below, does it make sense without i_bisect_taylor? *)
(* 
Fact compare_with_coqapprox (x : R) : -1 <= x <= 1 -> R_sqrt.sqrt (2 + x^2) <= 0.
Proof.
  intros.
  (* ignore the first one with native_compute, which needs to be initialised *)
  time try interval with (i_native_compute, i_depth 1, i_bisect_taylor x 10, i_prec 64).
  time try interval with (i_native_compute, i_depth 1, i_bisect_taylor x 20, i_prec 64).
  time try interval with (i_native_compute, i_depth 1, i_bisect_taylor x 30, i_prec 64).
  time try interval with (i_native_compute, i_depth 1, i_bisect_taylor x 40, i_prec 64).
  time try interval with (i_native_compute, i_depth 1, i_bisect_taylor x 50, i_prec 64).
  time try interval with (i_native_compute, i_depth 1, i_bisect_taylor x 60, i_prec 64).
  time try interval with (i_native_compute, i_depth 1, i_bisect_taylor x 70, i_prec 64).
  time try interval with (i_native_compute, i_depth 1, i_bisect_taylor x 80, i_prec 64).
  time try interval with (i_native_compute, i_depth 1, i_bisect_taylor x 90, i_prec 64).
  time try interval with (i_native_compute, i_depth 1, i_bisect_taylor x 100, i_prec 64).
  time try interval with (i_native_compute, i_depth 1, i_bisect_taylor x 110, i_prec 64).
  time try interval with (i_native_compute, i_depth 1, i_bisect_taylor x 120, i_prec 64).
  time try interval with (i_native_compute, i_depth 1, i_bisect_taylor x 130, i_prec 64).
  time try interval with (i_native_compute, i_depth 1, i_bisect_taylor x 140, i_prec 64).
  time try interval with (i_native_compute, i_depth 1, i_bisect_taylor x 150, i_prec 64).
  time try interval with (i_native_compute, i_depth 1, i_bisect_taylor x 160, i_prec 64).
  time try interval with (i_native_compute, i_depth 1, i_bisect_taylor x 170, i_prec 64).
  time try interval with (i_native_compute, i_depth 1, i_bisect_taylor x 180, i_prec 64).
  time try interval with (i_native_compute, i_depth 1, i_bisect_taylor x 190, i_prec 64).
  time try interval with (i_native_compute, i_depth 1, i_bisect_taylor x 200, i_prec 64).
Abort.
*)

Definition NearAbsRem01 (deg : Z) (eps: Q) :=
  LET Rem01 ::= @NearAbs F01 deg eps IN
  ret (width (mrange (Rem01 - mid))).

Time Eval vm_compute in (NearAbsRem01  4 0.01).
Time Eval vm_compute in (NearAbsRem01  5 0.01).
Time Eval vm_compute in (NearAbsRem01  6 0.01).
Time Eval vm_compute in (NearAbsRem01  7 0.01).
Time Eval vm_compute in (NearAbsRem01  8 0.01).
Time Eval vm_compute in (NearAbsRem01  9 0.01).
Time Eval vm_compute in (NearAbsRem01 10 0.01).
Time Eval vm_compute in (NearAbsRem01 11 0.01).
Time Eval vm_compute in (NearAbsRem01 12 0.01).
Time Eval vm_compute in (NearAbsRem01 13 0.01).
Time Eval vm_compute in (NearAbsRem01 14 0.01).
Time Eval vm_compute in (NearAbsRem01 15 0.01).
Time Eval vm_compute in (NearAbsRem01 16 0.01).
Time Eval vm_compute in (NearAbsRem01 17 0.01).
Time Eval vm_compute in (NearAbsRem01 18 0.01).
Time Eval vm_compute in (NearAbsRem01 19 0.01).
Time Eval vm_compute in (NearAbsRem01 20 0.01).

Time Eval vm_compute in (NearAbsRem01  8 0.001).
Time Eval vm_compute in (NearAbsRem01  9 0.001).
Time Eval vm_compute in (NearAbsRem01 10 0.001).
Time Eval vm_compute in (NearAbsRem01 11 0.001).
Time Eval vm_compute in (NearAbsRem01 12 0.001).
Time Eval vm_compute in (NearAbsRem01 13 0.001).
Time Eval vm_compute in (NearAbsRem01 14 0.001).
Time Eval vm_compute in (NearAbsRem01 15 0.001).
Time Eval vm_compute in (NearAbsRem01 16 0.001).
Time Eval vm_compute in (NearAbsRem01 18 0.001).
Time Eval vm_compute in (NearAbsRem01 20 0.001).
Time Eval vm_compute in (NearAbsRem01 22 0.001).
Time Eval vm_compute in (NearAbsRem01 24 0.001).
Time Eval vm_compute in (NearAbsRem01 26 0.001).
Time Eval vm_compute in (NearAbsRem01 28 0.001).
Time Eval vm_compute in (NearAbsRem01 30 0.001).

Time Eval vm_compute in (NearAbsRem01 14 0.0001).
Time Eval vm_compute in (NearAbsRem01 15 0.0001).
Time Eval vm_compute in (NearAbsRem01 16 0.0001).
Time Eval vm_compute in (NearAbsRem01 17 0.0001).
Time Eval vm_compute in (NearAbsRem01 18 0.0001).
Time Eval vm_compute in (NearAbsRem01 19 0.0001).
Time Eval vm_compute in (NearAbsRem01 20 0.0001).
Time Eval vm_compute in (NearAbsRem01 21 0.0001).
Time Eval vm_compute in (NearAbsRem01 22 0.0001).
Time Eval vm_compute in (NearAbsRem01 23 0.0001).
Time Eval vm_compute in (NearAbsRem01 24 0.0001).
Time Eval vm_compute in (NearAbsRem01 25 0.0001).
Time Eval vm_compute in (NearAbsRem01 26 0.0001).
Time Eval vm_compute in (NearAbsRem01 27 0.0001).
Time Eval vm_compute in (NearAbsRem01 28 0.0001).
Time Eval vm_compute in (NearAbsRem01 30 0.0001).#
Time Eval vm_compute in (NearAbsRem01 32 0.0001).

Fact coqapprox_compare (x : R) : 0 <= x <= 1 -> R_sqrt.sqrt (1/100 + x^2) - x <= 1/10*(101/100).
Proof.
   intros.
   Time interval with (i_depth 60, i_bisect x, i_prec 64).
Qed.



Definition NearAbsRem' (deg: Z) (eps: Q) :=
  (
  LET f11 ::= NearAbs F11 deg eps IN
  let fl := f11 + mid in
  let fr := f11 - mid in
  ret (meval fl (bnd (fromZ (-1)) 0),
       meval fr (bnd 0 1)),
  LET f10 ::= NearAbs F10 deg eps IN
  LET f01 ::= NearAbs F01 deg eps IN
  let gl := f10 + mid in
  let gr := f01 - mid in
  ret (mrange gl, mrange gr)
  ).

(* TOCHECK: we get errors... *)
Eval vm_compute in (NearAbsRem' 40 0.01  ). (* [.1002] *)
Eval vm_compute in (NearAbsRem' 40 0.001 ). (* [.0317] *)
Eval vm_compute in (NearAbsRem' 10 0.0001). (* nan *)
Eval vm_compute in (NearAbsRem' 15 0.0001). (* [.0123] *)
Eval vm_compute in (NearAbsRem' 20 0.0001). (* [.0107] *)
Eval vm_compute in (NearAbsRem' 40 0.0001). (* [.0100] *)
