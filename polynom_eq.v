(** * Newton method for certifying solutions of polynomial functional equations *)

Require Import Coquelicot.Coquelicot.
Require Import posreal_complements cball domfct banach.
Require Import vectorspace taylor.

Set Universe Polymorphism.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Newton operator *)
Definition opnewton {C: Ops0} (P : list C) (A : C) := ssub sid (sscal A P).

Section TubePolyn.
Variable (I : R -> Prop).
Notation "{R,I -> R}" := (@domfct_CompleteSpace R_CompleteSpace R_CompleteSpace I).

(** auxiliary lemmas about convexity *)
Lemma Rinterval_convex (a b u : R) :
  a <= u <= b -> exists eta,  0 <= eta <= 1 /\ u = a + eta * (b - a).
Proof.
  intros [Hle Hge]. exists ((u-a)/(b-a)); case (Req_dec a b) => Hab.
  + move : Hle Hge; rewrite Hab => Hle Hge; apply Rle_antisym in Hle => //.
    split; rewrite Hle /=; lra.
    have Hbgta : a < b. apply (Rle_trans a u b) in Hle; inversion Hle; by [].
    split; simpl. split.
  + apply Rdiv_le_0_compat; lra. 
  + apply (Rdiv_le_1 (u-a) (b-a)); lra.
  + field; lra.
Qed.

Lemma Rabs_convex v s1 s2 r eta:
  0 <= eta <= 1 ->
  Rabs (v  - s1) <= r ->  Rabs (v - s2) <= r ->
  Rabs (v - (s1 + eta * (s2 - s1))) <= r.
Proof.
  intros [Heta_le Heta_ge] Hs1 Hs2.
  replace ( _ - ( _ + _)) with ( (1-eta)*(v  - s1) + eta * ( v - s2)). 2: simpl; lra.
  have H1meta : 0 <= 1 - eta. lra.
  eapply Rle_trans. apply Rabs_triang. rewrite !Rabs_mult.
  replace r with ((1-eta)*r + eta * r). 2: simpl;lra.
  apply Rplus_le_compat ; rewrite Rabs_pos_eq => //; apply Rmult_le_compat_l => //; 
    try apply Hs1 => //; try apply Hs2 => //.
Qed.

Lemma newton (F: list (R -> R)) (phi A: R -> R) (d r lambda: R) :
  (forall s: R -> R, (forall t , I t -> Rabs (phi t - s t) <= r) ->
        forall t, I t -> Rabs (eval' (derive (opnewton F A)) s t) <= lambda) ->
  (forall t, I t ->  Rabs (A t * eval' F phi t) <= d) ->
  0 <= lambda < 1 -> 0 <= d -> 0 <= r -> d + lambda * r <= r ->
  (exists f: R -> R, forall t, I t  ->  eval' F f t = 0 /\ Rabs (f t - phi t) <= d / (1 - lambda)).
Proof.
  move => Hlambda Hd Hl Hd0 Hr0 Hdlr.
  set lambda0 := mknonnegreal (proj1 Hl).
  set d0 := mknonnegreal Hd0.
  have Hbound : 0 <= d / (1 - lambda). apply Rle_div_r; lra. 
  set b0 := mknonnegreal Hbound.
  set SB := mkSBall (phi : {R,I -> R}) d0 b0.
  set N : {R,I -> R} -> {R,I -> R} := fun s t => eval' (opnewton F A) s t.
  have Hdlr' : d / (1 - lambda) <= r. apply Rle_div_l; lra. 
  have SBP : SBallProp N lambda0 SB.
   apply mkSBallProp.
  + move => s1 s2 r' SBs1 SBs2 Hs1s2.

    apply R_dcballE => t It. rewrite /N. rewrite -2!eval_apply. 
    move : (MVT_gen (eval (apply (opnewton F A) t)) (s1 t) (s2 t) (eval (apply (derive (opnewton F A)) t))) =>  [ x Ineq  | x Ineq  | u [ Ineq Hmv ] ]. 
    - rewrite apply_derive. apply is_derive_eval. 
    - apply eval_cont_basis, M_cont. 
    - rewrite Hmv.
      
      move : (Rinterval_convex Ineq) => [eta] [Heta Hu]. rewrite Hu.
      have Hconvex : (forall t : R, I t -> Rabs (phi t - (fun t=>(Rmin (s1 t) (s2 t) + eta * (Rmax (s1 t) (s2 t) - Rmin (s1 t) (s2 t)))) t) <= r).
      move => t0 It0;
      rewrite /Rmin /Rmax; destruct (Rle_dec (s1 t0) (s2 t0)); apply Rabs_convex => //;
      by move : It0; apply R_dcballE, cball_sym, (cball_le Hdlr').

      move: (Hlambda (fun t=> (Rmin (s1 t) (s2 t) + eta * (Rmax (s1 t) (s2 t) - Rmin (s1 t) (s2 t)))) Hconvex t It) => Hlambda'.
      rewrite Rabs_mult /=. apply Rmult_le_compat. apply Rabs_pos. apply Rabs_pos. 
      by move : Hlambda'; rewrite -eval_apply.
      by move : It; apply R_dcballE.      
      
  + apply cball_sym, R_dcballE => t It /=.
    replace ( _ - _ ) with (A t * eval' F phi t). auto.
    rewrite /N /opnewton eval_sub_RinR eval_scal_RinR /= /f_bin /f_cst. lra. 
  + simpl. replace ( _ + _ ) with ( d / (1 - lambda)) => /=. apply Rle_refl.
    field. lra. 

  have HA t : I t -> A t <> 0.
    have Ht0 : forall t0 : R , I t0 -> Rabs (phi t0 - phi t0) <= r.
      move => t0 IT0; by rewrite Rminus_eq_0 Rabs_R0.  
    move => It HAt; move : (Hlambda phi Ht0 t It).
    rewrite /opnewton -eval'_apply apply_derive evalE eval_derive.
    rewrite apply_sub apply_scal apply_id.
    rewrite (Derive_ext _ (fun x => x - (A t) * eval (apply F t) x)).
    rewrite Derive_minus. rewrite Derive_mult. rewrite Derive_id Derive_const HAt.
    replace (1 - _) with 1%R => /=. rewrite Rabs_pos_eq => //=. lra. lra.
    apply ex_derive_const. apply eval_ex_derive. apply ex_derive_id.
    apply ex_derive_mult. apply ex_derive_const. apply eval_ex_derive. 
    by move => x; rewrite eval_sub eval_id eval_scal.  
    
    move: (BF_lim_is_fixpoint (proj2 Hl: lambda0 < 1)  SBP)
            (BF_lim_inside_sball (proj2 Hl: lambda0 < 1) SBP).

  set bf := lim (banach.BF N lambda0 SB). rewrite /SBall_pred /=.   
  move => /Rdomfct_close Hbanach_fix /R_dcballE Hbanach_bound; rewrite /N in Hbanach_fix.
  exists bf; split.

  + move : (Hbanach_fix t). rewrite /opnewton.
    rewrite eval_sub_RinR eval_scal_RinR eval_id_RinR /=.  
    intro Hb; specialize (Hb H); specialize (HA _ H). clear -Hb HA.
    have H': (A t * eval' F bf t = 0)%R by lra.
    apply Rmult_integral in H'. tauto. 
  + by apply Hbanach_bound.
Qed.

End TubePolyn.
