Require Import ZArith Reals Psatz.
Require Import ssreflect.

Require Import Coquelicot.Coquelicot.
Require Import posreal_complements cball domfct contraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TubeDiv.

Variable (I : R -> Prop).
Notation "{R,I -> R}" := (@domfct_CompleteSpace R_CompleteSpace R_CompleteSpace I).
Notation dball := (@ball {R,I -> R}).
Notation dcball := (@cball {R,I -> R}).
Notation dball0 := (@ball {R,I -> R} (fun _ => 0)).
Notation dcball0 := (@cball {R,I -> R} (fun _ => 0)).

Lemma newton (f g h w : R -> R) mu b :
  (forall t, I t -> Rabs (1 - w t * g t) <= mu) ->
  (forall t, I t -> Rabs (w t * (g t * h t - f t)) <= b) ->
  0 <= mu < 1 -> 0 <= b -> 
  forall t, I t -> Rabs (h t - f t / g t) <= b / (1 - mu).
Proof.
  move => Hmu Hb [Hmu0 Hmu1] Hb0.
  apply R_dcballE, cball_sym.
  set mmu := mknonnegreal Hmu0; set bb := mknonnegreal Hb0.
  have Hr : 0 <= b / (1 - mu)
    by apply Rdiv_le_0_compat => //; lra.
  set r := mknonnegreal Hr.
  have Hw t : I t -> w t <> 0
    by move => It Hwt; move: (Hmu t It); rewrite Hwt Rmult_0_l Rminus_0_r Rabs_R1; lra.
  have Hg t : I t -> g t <> 0
    by move => It Hgt; move: (Hmu t It); rewrite Hgt Rmult_0_r Rminus_0_r Rabs_R1; lra.
  set F : {R,I -> R} -> {R,I -> R} := fun k t => k t - w t * (g t * k t - f t).
  set SB := mkSBall (h : {R,I -> R}) bb r.
  have SBP : SBallProp F mmu SB.
    apply mkSBallProp => /=.
    + move => k1 k2 d _ _ /R_dcballE Hk.
      apply R_dcballE => t It.
      replace (_-_) with ((1 - w t * g t) * (k2 t - k1 t)); last by rewrite /F; ring.
      rewrite Rabs_mult; apply Rmult_le_compat; try apply Rabs_pos; auto.
    + apply R_dcballE => t It /=.
      replace (_-_) with (-(w t * (g t * h t - f t))); last by rewrite /F; ring.
      rewrite Rabs_Ropp; auto.
    + field_simplify; lra.
  move: (BF_lim_is_fixpoint (Hmu1 : mmu < 1) SBP) (BF_lim_inside_sball (Hmu1 : mmu < 1) SBP).
  set bf := lim (BF F mmu SB); rewrite /SBall_pred /=.
  move => /Rdomfct_close Hbf.
  apply domfct_cball_ext_r => t It.
  apply Rmult_eq_reg_l with (g t); auto; field_simplify; auto. 
  apply Rminus_diag_uniq, Rmult_eq_reg_l with (w t); auto. 
  move: (Hbf t It); rewrite /F /=; lra.
Qed.

End TubeDiv.

