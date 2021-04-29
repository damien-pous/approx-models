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

Section Exemple1.

Section s.
Variable N : Z.
Variable eps : forall {C : Ops1}, C. Arguments eps {C}.
Context {C : Ops1} {F: FunOps C}.
Definition NearAbs : E F := msqrt N (mcst eps + mid * mid).
End s.

Definition D10: Domain := DZ (-1) 0.
Definition D01: Domain := DZ 0 1.

(* implicit use of [Iprimitive.nbh] below *)
Definition F11 := MFunOps chebyshev.basis.
Definition F10 := MFunOps (rescale D10 chebyshev.basis).
Definition F01 := MFunOps (rescale D01 chebyshev.basis).

Definition wrem {nbh: NBH} (x: E (Model II)) := x >>= fun x => ret (width (rem x)). 

(* First, compute rigorous approximations over [-1,1] and check remainders *)

(* eps = 1/10 *)
Time Eval vm_compute in (wrem (@NearAbs 10 (fun C => 1/fromZ 10) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 20 (fun C => 1/fromZ 10) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 30 (fun C => 1/fromZ 10) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 40 (fun C => 1/fromZ 10) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 50 (fun C => 1/fromZ 10) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 60 (fun C => 1/fromZ 10) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 70 (fun C => 1/fromZ 10) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 80 (fun C => 1/fromZ 10) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 90 (fun C => 1/fromZ 10) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 100 (fun C => 1/fromZ 10) II F11)).

(* eps = 1/100 *)
Time Eval vm_compute in (wrem (@NearAbs 10 (fun C => 1/fromZ 100) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 20 (fun C => 1/fromZ 100) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 30 (fun C => 1/fromZ 100) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 40 (fun C => 1/fromZ 100) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 50 (fun C => 1/fromZ 100) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 60 (fun C => 1/fromZ 100) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 70 (fun C => 1/fromZ 100) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 80 (fun C => 1/fromZ 100) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 90 (fun C => 1/fromZ 100) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 100 (fun C => 1/fromZ 100) II F11)).

(* eps = 1/1000 *)
Time Eval vm_compute in (wrem (@NearAbs 10 (fun C => 1/fromZ 1000) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 20 (fun C => 1/fromZ 1000) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 30 (fun C => 1/fromZ 1000) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 40 (fun C => 1/fromZ 1000) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 50 (fun C => 1/fromZ 1000) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 60 (fun C => 1/fromZ 1000) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 70 (fun C => 1/fromZ 1000) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 80 (fun C => 1/fromZ 1000) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 90 (fun C => 1/fromZ 1000) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 100 (fun C => 1/fromZ 1000) II F11)).

(* eps = 1/10000 *)
(* TOCHECK: here we get nan values *)
Time Eval vm_compute in (wrem (@NearAbs 10 (fun C => 1/fromZ 10000) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 20 (fun C => 1/fromZ 10000) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 30 (fun C => 1/fromZ 10000) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 40 (fun C => 1/fromZ 10000) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 50 (fun C => 1/fromZ 10000) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 60 (fun C => 1/fromZ 10000) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 70 (fun C => 1/fromZ 10000) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 80 (fun C => 1/fromZ 10000) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 90 (fun C => 1/fromZ 10000) II F11)).
Time Eval vm_compute in (wrem (@NearAbs 100 (fun C => 1/fromZ 10000) II F11)).

(* compare timings with coqapprox, with eps=2 *)

(* ignore the first one with native_compute, which needs to be initialised *)
Time Eval native_compute in (wrem (@NearAbs 10 (fun C => fromZ 2) II F11)).
Time Eval native_compute in (wrem (@NearAbs 10 (fun C => fromZ 2) II F11)).
Time Eval native_compute in (wrem (@NearAbs 20 (fun C => fromZ 2) II F11)).
Time Eval native_compute in (wrem (@NearAbs 30 (fun C => fromZ 2) II F11)).
Time Eval native_compute in (wrem (@NearAbs 40 (fun C => fromZ 2) II F11)).
Time Eval native_compute in (wrem (@NearAbs 50 (fun C => fromZ 2) II F11)).
Time Eval native_compute in (wrem (@NearAbs 60 (fun C => fromZ 2) II F11)).
Time Eval native_compute in (wrem (@NearAbs 70 (fun C => fromZ 2) II F11)).
Time Eval native_compute in (wrem (@NearAbs 80 (fun C => fromZ 2) II F11)).
Time Eval native_compute in (wrem (@NearAbs 90 (fun C => fromZ 2) II F11)).
Time Eval native_compute in (wrem (@NearAbs 100 (fun C => fromZ 2) II F11)).
Time Eval native_compute in (wrem (@NearAbs 110 (fun C => fromZ 2) II F11)).
Time Eval native_compute in (wrem (@NearAbs 120 (fun C => fromZ 2) II F11)).
Time Eval native_compute in (wrem (@NearAbs 130 (fun C => fromZ 2) II F11)).
Time Eval native_compute in (wrem (@NearAbs 140 (fun C => fromZ 2) II F11)).
Time Eval native_compute in (wrem (@NearAbs 150 (fun C => fromZ 2) II F11)).
Time Eval native_compute in (wrem (@NearAbs 160 (fun C => fromZ 2) II F11)).
Time Eval native_compute in (wrem (@NearAbs 170 (fun C => fromZ 2) II F11)).
Time Eval native_compute in (wrem (@NearAbs 180 (fun C => fromZ 2) II F11)).
Time Eval native_compute in (wrem (@NearAbs 190 (fun C => fromZ 2) II F11)).
Time Eval native_compute in (wrem (@NearAbs 200 (fun C => fromZ 2) II F11)).

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

Definition NearAbsRem01 eps (N : Z) :=
  LET Rem01 ::= @NearAbs N eps II F01 IN
  ret (width (mrange (Rem01 - mid))).

Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 100) 4).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 100) 5).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 100) 6).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 100) 7).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 100) 8).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 100) 9).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 100) 10).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 100) 11).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 100) 12).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 100) 13).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 100) 14).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 100) 15).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 100) 16).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 100) 17).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 100) 18).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 100) 19).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 100) 20).

Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 1000) 8).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 1000) 9).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 1000) 10).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 1000) 11).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 1000) 12).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 1000) 13).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 1000) 14).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 1000) 15).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 1000) 16).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 1000) 18).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 1000) 20).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 1000) 22).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 1000) 24).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 1000) 26).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 1000) 28).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 1000) 30).

Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 10000) 14).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 10000) 15).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 10000) 16).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 10000) 17).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 10000) 18).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 10000) 19).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 10000) 20).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 10000) 21).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 10000) 22).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 10000) 23).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 10000) 24).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 10000) 25).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 10000) 26).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 10000) 27).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 10000) 28).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 10000) 30).
Time Eval vm_compute in (NearAbsRem01 (fun C => 1/fromZ 10000) 32).

Fact coqapprox_compare (x : R) : 0 <= x <= 1 -> R_sqrt.sqrt (1/100 + x^2) - x <= 1/10*(101/100).
Proof.
   intros.
   Time interval with (i_depth 60, i_bisect x, i_prec 64).
Qed.



Definition NearAbsRem' eps (N : Z) :=
  (
  LET f11 ::= @NearAbs N eps II F11 IN
  let fl := f11 + mid in
  let fr := f11 - mid in
  ret (meval fl (bnd (fromZ (-1)) 0),
       meval fr (bnd 0 1)),
  LET f10 ::= @NearAbs N eps II F10 IN
  LET f01 ::= @NearAbs N eps II F01 IN
  let gl := f10 + mid in
  let gr := f01 - mid in
  ret (mrange gl, mrange gr)
  ).

(* TOCHECK: we get errors... *)
Eval vm_compute in (NearAbsRem' (fun C => 1/fromZ 100) 40).   (* [.1002] *)
Eval vm_compute in (NearAbsRem' (fun C => 1/fromZ 1000) 40).  (* [.0317] *)
Eval vm_compute in (NearAbsRem' (fun C => 1/fromZ 10000) 10). (* nan *)
Eval vm_compute in (NearAbsRem' (fun C => 1/fromZ 10000) 15). (* [.0123] *)
Eval vm_compute in (NearAbsRem' (fun C => 1/fromZ 10000) 20). (* [.0107] *)
Eval vm_compute in (NearAbsRem' (fun C => 1/fromZ 10000) 40). (* [.0100] *)

End Exemple1.
