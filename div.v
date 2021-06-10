(** * Newton method for computing division *)

Require Import ZArith Reals Psatz.
Require Import ssreflect.
Require Import Coquelicot.Coquelicot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TubeDiv.

(** D is the domain of the considered functions *)
Variable (D : R -> Prop).


(** this is purely a lemma about real numbers and functions, no intervals or models involved *)
Lemma newton (f g h w : R -> R) mu b :
  (forall t, D t -> Rabs (1 - w t * g t) <= mu) ->
  (forall t, D t -> Rabs (w t * (g t * h t - f t)) <= b) ->
  0 <= mu < 1 -> 0 <= b -> 
  forall t, D t -> g t <> 0 /\ Rabs (h t - f t / g t) <= b / (1 - mu).
Proof.
  (** proof script by Quentin Corradi (M2 student at ENS Lyon, autumn 2020) *)
  intros Hmu Hb Dmu Db t Dt.
  assert (Hw: forall t, D t -> w t <> 0).
   intros t' Dt' Hw0. specialize (Hmu t' Dt').
   replace (Rabs (1 - w t'*g t')) with 1 in Hmu. lra.
   rewrite Hw0 Rmult_0_l Rminus_0_r Rabs_R1 //.
  assert (Hg: forall t, D t -> g t <> 0).
   intros t' Dt' Hg0. specialize (Hmu t' Dt').
   replace (Rabs (1 - w t'*g t')) with 1 in Hmu. lra.
   rewrite Hg0 Rmult_0_r Rminus_0_r Rabs_R1 //.
  split. by apply Hg. 
  apply Rmult_le_reg_l with (Rabs (w t*g t)).
  apply Rabs_pos_lt, Rmult_integral_contrapositive. now auto.
  apply Rle_trans with b. rewrite -Rabs_mult.
  replace (w t*g t*(h t - f t/g t)) with (w t*(g t*h t - f t)) by (field; auto). now auto.
  apply Rmult_le_reg_r with (1 - mu). lra.
  replace (Rabs (w t*g t)*(b/(1 - mu))*(1 - mu)) with (b*Rabs (w t*g t)) by (field; lra).
  apply Rmult_le_compat_l. assumption.
  apply Rplus_le_reg_r with (mu - Rabs (w t*g t)).
  ring_simplify. apply Rle_trans with (Rabs (1 - w t*g t)).
  replace (-Rabs (w t*g t) + 1) with (Rabs 1 - Rabs (w t*g t)) by (rewrite -{2}Rabs_R1; ring).
  apply Rabs_triang_inv. now auto.
Qed.

End TubeDiv.

