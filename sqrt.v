(** * Newton method for computing square root *)

Require Import ZArith Reals Psatz.
Require Import ssreflect.
Require Import Coquelicot.Coquelicot.
Require Import posreal_complements cball domfct banach.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Quadratic.

Variable (b mu0 mu1 : R).
Hypothesis Hb_0 : 0 <= b.
Hypothesis Hmu0_0 : 0 <= mu0.
Hypothesis Hmu0_1 : mu0 < 1.
Hypothesis Hmu1_0 : 0 < mu1.

Definition quad r := b + (mu0 + 2 * mu1 * r) * r - r.

Definition delta := (1 - mu0) ^ 2 - 8 * b * mu1.
Definition rmin := (1 - mu0 - sqrt delta) / (4 * mu1).
Definition rmax := (1 - mu0 + sqrt delta) / (4 * mu1).

Lemma rmin_rmax_lt : 0 <= delta -> rmin <= rmax.
Proof.
  move => Hdelta; rewrite /rmin /rmax.
  apply Rmult_le_compat_r.
  apply Rlt_le, Rinv_0_lt_compat; lra.
  by move: (sqrt_positivity _ Hdelta); lra.
Qed.

Lemma rmin_ge_0 : 0 <= delta -> 0 <= rmin.
Proof.
  move => Hdelta; rewrite /rmin.
  apply Rdiv_le_0_compat; last lra.
  apply Rge_le; apply Rge_minus. rewrite -(sqrt_Rsqr (1 - mu0)); last lra.
  apply Rle_ge; apply sqrt_le_1_alt; rewrite /delta.
  have H : 0 <= 8 * b * mu1 by apply Rmult_le_pos; lra.
  rewrite /Rsqr /=; move: H; lra.
Qed.

Lemma rmax_gt_0 : 0 <= delta -> 0 <= rmax.
Proof.
  move => Hdelta; eapply Rle_trans.
  by apply rmin_ge_0.
  by apply rmin_rmax_lt.
Qed.

Definition quad_fact r := 2 * mu1 * (r - rmin) * (r - rmax).

Lemma quad_quad_fact : 0 <= delta -> forall r, quad r = quad_fact r.
Proof.
  move => Hdelta r; rewrite /quad /quad_fact /rmin /rmax.
  field_simplify; last lra.
  replace ((sqrt delta)^2) with (sqrt delta * sqrt delta); last by ring.
  rewrite sqrt_def; last lra; rewrite /delta; field; lra.
Qed.

Lemma quad_rmin_0 : 0 <= delta -> quad rmin = 0.
Proof. by move => Hdelta; rewrite quad_quad_fact => //; rewrite /quad_fact; ring. Qed.

Lemma quad_rmax_0 : 0 <= delta -> quad rmax = 0.
Proof. by move => Hdelta; rewrite quad_quad_fact => //; rewrite /quad_fact; ring. Qed.

Lemma quad_le_0 : 0 <= delta -> forall r, rmin  <= r <= rmax -> quad r <= 0.
Proof.
  move => Hdelta r [Hr1 Hr2]; rewrite quad_quad_fact /quad_fact => //.
  apply Rmult_le_0_l; last by lra.
  apply Rmult_le_pos; lra.
Qed.

End Quadratic.


Section TubeSqrt.
Variable (I : R -> Prop).
Notation "{R,I -> R}" := (@domfct_CompleteSpace R_CompleteSpace R_CompleteSpace I).


Lemma newton (f h w : R -> R) mu0 mu1 b :
  (forall t, I t -> Rabs (1 - 2 * w t * h t) <= mu0) ->
  (forall t, I t -> Rabs (w t) <= mu1) ->
  (forall t, I t -> Rabs (w t * ((h t)^2 - f t)) <= b) ->
  0 <= mu0 < 1 -> 0 < mu1 -> 0 <= b -> 0 <= delta b mu0 mu1 -> mu0 + 2 * mu1 * rmin b mu0 mu1 < 1 ->
  (forall t1 t2 t3, t1 <= t2 <= t3 -> I t1 -> I t3 -> I t2) ->
  (forall t, I t -> continuity_pt w t) -> (exists t0, I t0 /\ w t0 > 0) ->
  forall t, I t -> Rabs (h t - sqrt (f t)) <= rmin b mu0 mu1.
Proof.
  move => Hmu0 Hmu1 Hb [Hmu0_0 Hmu0_1] Hmu1_0 Hb_0 Hdelta Hmu_1 Iconvex Hwcont [t0 [It0 Hwt0]].
  set mmu0 := mknonnegreal Hmu0_0; set mmu1 := mkposreal Hmu1_0; set bb := mknonnegreal Hb_0.
  apply R_dcballE, cball_sym.
  have Hw' t : I t -> w t <> 0
    by move => It Hwt; move: (Hmu0 t It); rewrite Hwt Rmult_0_r Rmult_0_l Rminus_0_r Rabs_R1; lra.
  have Hw t : I t -> w t > 0.
    move => It.
    case: (Rle_lt_dec (w t) 0); last lra; move => /Rle_lt_or_eq_dec [Hwt | Hwt]; last by move: (Hw' t It).
    case: (Rle_lt_dec t0 t) => [ | Ht0t]; first move => /Rle_lt_or_eq_dec [Ht0t | Ht0t].
    + have HH : {t' : R | t0 <= t' <= t /\ - w t' = 0}. apply Ranalysis5.IVT_interv; try lra.
      by move => t' Ht'; eapply continuity_pt_opp, Hwcont, Iconvex; first apply Ht'.
      by case: HH => t' [Ht' Hwt']; exfalso; apply (Hw' t'); last lra; eapply Iconvex; try apply Ht'.
    + move: Hwt0; rewrite Ht0t; lra.
    + have HH : {t' : R | t <= t' <= t0 /\ w t' = 0}. apply Ranalysis5.IVT_interv; try lra.
      by move => t' Ht'; eapply Hwcont, Iconvex; first apply Ht'.
      by case: HH => t' [Ht' Hwt']; exfalso; apply (Hw' t'); last lra; eapply Iconvex; try apply Ht'.
  have Hh t : I t -> h t > 0.
    move => It; case: (Rle_lt_dec (h t) 0) => Hht; last lra.
    have HH : w t * h t <= 0 by apply Rmult_le_0_l => //; apply Rlt_le, Hw.
    move: (Hmu0 t It); rewrite Rmult_assoc Rabs_pos_eq; lra.
  set F : {R,I -> R} -> {R,I -> R} := fun k t => k t - w t * ((k t) ^ 2 - f t).
  have Hr : 0 <= rmin b mu0 mu1 by apply rmin_ge_0.
  set r := mknonnegreal Hr.
  set SB := mkSBall (h : {R,I -> R}) bb r.
  set mu := (mmu0 + 2 * mmu1 * r)%:nonnegreal.
  have SBP : SBallProp F mu SB.
    apply mkSBallProp.
    + move => k1 k2 d /R_dcballE /= Hk1 /R_dcballE /= Hk2 /R_dcballE Hk.
      apply R_dcballE => t It.
      replace (_-_) with (((1 - 2 * w t * h t) + - w t * ((k1 t - h t) + (k2 t - h t))) * (k2 t - k1 t));
        last by rewrite /F; ring.
      rewrite Rabs_mult; apply Rmult_le_compat; try apply Rabs_pos; last by apply Hk.
      eapply Rle_trans; first apply Rabs_triang; apply Rplus_le_compat; first by apply Hmu0.
      rewrite Rabs_mult Rabs_Ropp.
      replace (_*_*_) with (mu1 * (r + r)); last by rewrite /=; ring.
      apply Rmult_le_compat; try apply Rabs_pos; first by apply Hmu1.
      by eapply Rle_trans; first apply Rabs_triang; apply Rplus_le_compat; [apply Hk1 | apply Hk2].
    + apply R_dcballE => t It /=.
      replace (_-_) with (-(w t * ((h t) ^ 2 - f t))); last by rewrite /F; ring.
      rewrite Rabs_Ropp; auto.
    + by apply Rminus_le; move: quad_rmin_0; rewrite /quad /= => ->; lra.
  move: (BF_lim_is_fixpoint (Hmu_1 : mu < 1) SBP) (BF_lim_inside_sball (Hmu_1 : mu < 1) SBP).
  set bf := lim (BF F mu SB); rewrite /SBall_pred /=.
  move => /Rdomfct_close Hbf /R_dcballE Hbf'.
  eapply domfct_cball_ext_r => t It; last by apply R_dcballE, Hbf'.
  have Hsqr : bf t ^ 2 = f t.
    apply Rminus_diag_uniq, Rmult_eq_reg_l with (w t); last by apply Hw'.
    move: (Hbf t It); rewrite Rmult_0_r /F /=; lra.
  rewrite /= -Hsqr /= Rmult_1_r sqrt_square => //.
  have Habs : Rabs (1 - 2 * w t * bf t) <= mu.
    replace (_-_) with ((1 - 2 * w t * h t) + -(2 * w t * (bf t - h t))); last by ring.
    eapply Rle_trans; first apply Rabs_triang; apply Rplus_le_compat; auto.
    rewrite Rabs_Ropp !Rabs_mult; apply Rmult_le_compat; first apply Rmult_le_pos; try apply Rabs_pos.
    apply Rmult_le_compat; try apply Rabs_pos; first by rewrite /= Rabs_pos_eq; lra.
    by apply Hmu1. by apply Hbf'.
  apply Rlt_le; case: (Rlt_le_dec 0 (bf t)) => // Habs'.
  have Habs'' : w t * bf t <= 0.
    by apply Rmult_le_0_l => //; apply Rlt_le, Hw.
  move: Habs; rewrite Rmult_assoc Rabs_pos_eq /mu /=; lra.
Qed.

End TubeSqrt.
