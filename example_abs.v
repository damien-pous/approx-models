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
  (* does not work without subdivision *)
  Fail interval.
  (* works with *)
  interval with (i_bisect x).
Qed.

Fact test1 x :
  let eps := 1/1000 in
  0 <= x <= 1 ->
  Rabs (f1 eps x - x) <= eps+1/10000.
Proof.
  intros eps H; subst eps; unfold f1.
  (* does not work without subdivision *)
  Fail interval.
  (* works with *)
  interval with (i_bisect x).
Qed.


(** * with our library *)
Require Import approx rescale intervals errors.
Require chebyshev.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Section s. *)
(* Variable N : Z. *)
(* Variable eps : forall {C : Ops1}, C. *)
(* Arguments eps {C}. *)
(* Context {C : Ops1} {F: FunOps C}. *)
(* Definition NearAbs : E F := msqrt N (mcst eps + mid * mid). *)
(* End s. *)

Definition D10: Domain := DZ (-1) 0.
Definition D01: Domain := DZ 0 1.

(* implicit use of [Iprimitive.nbh] below *)
Definition F11 := approx.model chebyshev.basis.
Definition F10 := approx.model (rescale.to D10 chebyshev.basis).
Definition F01 := approx.model (rescale.to D01 chebyshev.basis).

Definition wrem (x: E (Model II)) := x >>= fun x => ret (width (rem x)). 

Definition NearAbs (MM: FunOps) (deg: Z) (eps: II): E MM := msqrt deg (mcst eps + mid * mid). 



(* First, compute rigorous approximations over [-1,1] and check remainders *)

(* eps = 1/10 *)
Time Eval native_compute in (wrem (NearAbs F11  10 (1/fromZ 10))).
Time Eval native_compute in (wrem (NearAbs F11  20 (1/fromZ 10))).
Time Eval native_compute in (wrem (NearAbs F11  30 (1/fromZ 10))).
Time Eval native_compute in (wrem (NearAbs F11  40 (1/fromZ 10))).
Time Eval native_compute in (wrem (NearAbs F11  50 (1/fromZ 10))).
Time Eval native_compute in (wrem (NearAbs F11  60 (1/fromZ 10))).
Time Eval native_compute in (wrem (NearAbs F11  70 (1/fromZ 10))).
Time Eval native_compute in (wrem (NearAbs F11  80 (1/fromZ 10))).
Time Eval native_compute in (wrem (NearAbs F11  90 (1/fromZ 10))).
Time Eval native_compute in (wrem (NearAbs F11 100 (1/fromZ 10))).

(* eps = 1/100 *)
Time Eval native_compute in (wrem (NearAbs F11  10 (1/fromZ 100))).
Time Eval native_compute in (wrem (NearAbs F11  20 (1/fromZ 100))).
Time Eval native_compute in (wrem (NearAbs F11  30 (1/fromZ 100))).
Time Eval native_compute in (wrem (NearAbs F11  40 (1/fromZ 100))).
Time Eval native_compute in (wrem (NearAbs F11  50 (1/fromZ 100))).
Time Eval native_compute in (wrem (NearAbs F11  60 (1/fromZ 100))).
Time Eval native_compute in (wrem (NearAbs F11  70 (1/fromZ 100))).
Time Eval native_compute in (wrem (NearAbs F11  80 (1/fromZ 100))).
Time Eval native_compute in (wrem (NearAbs F11  90 (1/fromZ 100))).
Time Eval native_compute in (wrem (NearAbs F11 100 (1/fromZ 100))).

(* eps = 1/1000 *)
Time Eval native_compute in (wrem (NearAbs F11  10 (1/fromZ 1000))).
Time Eval native_compute in (wrem (NearAbs F11  20 (1/fromZ 1000))).
Time Eval native_compute in (wrem (NearAbs F11  30 (1/fromZ 1000))).
Time Eval native_compute in (wrem (NearAbs F11  40 (1/fromZ 1000))).
Time Eval native_compute in (wrem (NearAbs F11  50 (1/fromZ 1000))).
Time Eval native_compute in (wrem (NearAbs F11  60 (1/fromZ 1000))).
Time Eval native_compute in (wrem (NearAbs F11  70 (1/fromZ 1000))).
Time Eval native_compute in (wrem (NearAbs F11  80 (1/fromZ 1000))).
Time Eval native_compute in (wrem (NearAbs F11  90 (1/fromZ 1000))).
Time Eval native_compute in (wrem (NearAbs F11 100 (1/fromZ 1000))).

(* eps = 1/10000 *)
(* TOCHECK: we get errors *)
Time Eval native_compute in (wrem (NearAbs F11  10 (1/fromZ 10000))).
Time Eval native_compute in (wrem (NearAbs F11  20 (1/fromZ 10000))).
Time Eval native_compute in (wrem (NearAbs F11  30 (1/fromZ 10000))).
Time Eval native_compute in (wrem (NearAbs F11  40 (1/fromZ 10000))).
Time Eval native_compute in (wrem (NearAbs F11  50 (1/fromZ 10000))).
Time Eval native_compute in (wrem (NearAbs F11  60 (1/fromZ 10000))).
Time Eval native_compute in (wrem (NearAbs F11  70 (1/fromZ 10000))).
Time Eval native_compute in (wrem (NearAbs F11  80 (1/fromZ 10000))).
Time Eval native_compute in (wrem (NearAbs F11  90 (1/fromZ 10000))).
Time Eval native_compute in (wrem (NearAbs F11 100 (1/fromZ 10000))).
Time Eval native_compute in (wrem (NearAbs F11 200 (1/fromZ 10000))).

(* compare timings with coqapprox, with eps=2 *)

(* ignore the first one with native_compute, which needs to be initialised *)
Time Eval native_compute in (wrem (NearAbs F11  10 (fromZ 2))).
Time Eval native_compute in (wrem (NearAbs F11  10 (fromZ 2))).
Time Eval native_compute in (wrem (NearAbs F11  20 (fromZ 2))).
Time Eval native_compute in (wrem (NearAbs F11  30 (fromZ 2))).
Time Eval native_compute in (wrem (NearAbs F11  40 (fromZ 2))).
Time Eval native_compute in (wrem (NearAbs F11  50 (fromZ 2))).
Time Eval native_compute in (wrem (NearAbs F11  60 (fromZ 2))).
Time Eval native_compute in (wrem (NearAbs F11  70 (fromZ 2))).
Time Eval native_compute in (wrem (NearAbs F11  80 (fromZ 2))).
Time Eval native_compute in (wrem (NearAbs F11  90 (fromZ 2))).
Time Eval native_compute in (wrem (NearAbs F11 100 (fromZ 2))).
Time Eval native_compute in (wrem (NearAbs F11 110 (fromZ 2))).
Time Eval native_compute in (wrem (NearAbs F11 120 (fromZ 2))).
Time Eval native_compute in (wrem (NearAbs F11 130 (fromZ 2))).
Time Eval native_compute in (wrem (NearAbs F11 140 (fromZ 2))).
Time Eval native_compute in (wrem (NearAbs F11 150 (fromZ 2))).
Time Eval native_compute in (wrem (NearAbs F11 160 (fromZ 2))).
Time Eval native_compute in (wrem (NearAbs F11 170 (fromZ 2))).
Time Eval native_compute in (wrem (NearAbs F11 180 (fromZ 2))).
Time Eval native_compute in (wrem (NearAbs F11 190 (fromZ 2))).
Time Eval native_compute in (wrem (NearAbs F11 200 (fromZ 2))).

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

Definition NearAbsRem01 (deg : Z) (eps: II) :=
  LET Rem01 ::= @NearAbs F01 deg eps IN
  ret (width (mrange (Rem01 - mid))).

Time Eval vm_compute in (NearAbsRem01  4 (1/fromZ 100)).
Time Eval vm_compute in (NearAbsRem01  5 (1/fromZ 100)).
Time Eval vm_compute in (NearAbsRem01  6 (1/fromZ 100)).
Time Eval vm_compute in (NearAbsRem01  7 (1/fromZ 100)).
Time Eval vm_compute in (NearAbsRem01  8 (1/fromZ 100)).
Time Eval vm_compute in (NearAbsRem01  9 (1/fromZ 100)).
Time Eval vm_compute in (NearAbsRem01 10 (1/fromZ 100)).
Time Eval vm_compute in (NearAbsRem01 11 (1/fromZ 100)).
Time Eval vm_compute in (NearAbsRem01 12 (1/fromZ 100)).
Time Eval vm_compute in (NearAbsRem01 13 (1/fromZ 100)).
Time Eval vm_compute in (NearAbsRem01 14 (1/fromZ 100)).
Time Eval vm_compute in (NearAbsRem01 15 (1/fromZ 100)).
Time Eval vm_compute in (NearAbsRem01 16 (1/fromZ 100)).
Time Eval vm_compute in (NearAbsRem01 17 (1/fromZ 100)).
Time Eval vm_compute in (NearAbsRem01 18 (1/fromZ 100)).
Time Eval vm_compute in (NearAbsRem01 19 (1/fromZ 100)).
Time Eval vm_compute in (NearAbsRem01 20 (1/fromZ 100)).

Time Eval vm_compute in (NearAbsRem01  8 (1/fromZ 1000)).
Time Eval vm_compute in (NearAbsRem01  9 (1/fromZ 1000)).
Time Eval vm_compute in (NearAbsRem01 10 (1/fromZ 1000)).
Time Eval vm_compute in (NearAbsRem01 11 (1/fromZ 1000)).
Time Eval vm_compute in (NearAbsRem01 12 (1/fromZ 1000)).
Time Eval vm_compute in (NearAbsRem01 13 (1/fromZ 1000)).
Time Eval vm_compute in (NearAbsRem01 14 (1/fromZ 1000)).
Time Eval vm_compute in (NearAbsRem01 15 (1/fromZ 1000)).
Time Eval vm_compute in (NearAbsRem01 16 (1/fromZ 1000)).
Time Eval vm_compute in (NearAbsRem01 18 (1/fromZ 1000)).
Time Eval vm_compute in (NearAbsRem01 20 (1/fromZ 1000)).
Time Eval vm_compute in (NearAbsRem01 22 (1/fromZ 1000)).
Time Eval vm_compute in (NearAbsRem01 24 (1/fromZ 1000)).
Time Eval vm_compute in (NearAbsRem01 26 (1/fromZ 1000)).
Time Eval vm_compute in (NearAbsRem01 28 (1/fromZ 1000)).
Time Eval vm_compute in (NearAbsRem01 30 (1/fromZ 1000)).

Time Eval vm_compute in (NearAbsRem01 14 (1/fromZ 10000)).
Time Eval vm_compute in (NearAbsRem01 15 (1/fromZ 10000)).
Time Eval vm_compute in (NearAbsRem01 16 (1/fromZ 10000)).
Time Eval vm_compute in (NearAbsRem01 17 (1/fromZ 10000)).
Time Eval vm_compute in (NearAbsRem01 18 (1/fromZ 10000)).
Time Eval vm_compute in (NearAbsRem01 19 (1/fromZ 10000)).
Time Eval vm_compute in (NearAbsRem01 20 (1/fromZ 10000)).
Time Eval vm_compute in (NearAbsRem01 21 (1/fromZ 10000)).
Time Eval vm_compute in (NearAbsRem01 22 (1/fromZ 10000)).
Time Eval vm_compute in (NearAbsRem01 23 (1/fromZ 10000)).
Time Eval vm_compute in (NearAbsRem01 24 (1/fromZ 10000)).
Time Eval vm_compute in (NearAbsRem01 25 (1/fromZ 10000)).
Time Eval vm_compute in (NearAbsRem01 26 (1/fromZ 10000)).
Time Eval vm_compute in (NearAbsRem01 27 (1/fromZ 10000)).
Time Eval vm_compute in (NearAbsRem01 28 (1/fromZ 10000)).
Time Eval vm_compute in (NearAbsRem01 30 (1/fromZ 10000)).
Time Eval vm_compute in (NearAbsRem01 32 (1/fromZ 10000)).

Fact coqapprox_compare (x : R) : 0 <= x <= 1 -> R_sqrt.sqrt (1/100 + x^2) - x <= 1/10*(101/100).
Proof.
   intros.
   Time interval with (i_depth 60, i_bisect x, i_prec 64).
Qed.



Definition NearAbsRem' (deg: Z) (eps: II) :=
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
Eval vm_compute in (NearAbsRem' 40 (1/fromZ 100)  ). (* [.1002] *)
Eval vm_compute in (NearAbsRem' 40 (1/fromZ 1000) ). (* [.0317] *)
Eval vm_compute in (NearAbsRem' 10 (1/fromZ 10000)). (* nan *)
Eval vm_compute in (NearAbsRem' 15 (1/fromZ 10000)). (* [.0123] *)
Eval vm_compute in (NearAbsRem' 20 (1/fromZ 10000)). (* [.0107] *)
Eval vm_compute in (NearAbsRem' 40 (1/fromZ 10000)). (* [.0100] *)
