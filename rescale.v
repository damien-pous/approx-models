(** * Rescaling operation on bases *)

Require Import vectorspace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section r.
 Variable C: Ops1.
 Variable B: BasisOps_on C.
 Variables a c: C.
 Let hilo := hi - lo.
 Let ca := c - a.
 Let hiloca := hilo / ca.
 Let cahilo := ca / hilo.
 Let f (x: C) := a + (x-lo) * cahilo. (* f: [lo;hi] -> [a;b] *)
 Let g (y: C) := lo + (y-a) * hiloca. (* g: [a;b]   -> [lo;hi] *)
 Let r_id: list C := sscal cahilo bid + sscal (a-lo*cahilo) bone.
 Let r_eval (p: list C) (y: C) := beval p (g y).
 Let r_interpolate n h := interpolate n (fun x => h (f x)).
 Let r_integrate (p: list C) (a b: C): C := cahilo * bintegrate p (g a) (g b).
 Definition rescale_ops_on: BasisOps_on C :=
   {|
     lo := a;
     hi := c;
     bmul := bmul;
     bone := bone;
     bid := r_id;
     bintegrate := r_integrate;
     beval := r_eval;
     brange := brange;
     interpolate := r_interpolate;
   |}.
End r.

Lemma is_RInt_ext' (f: R->R) a a' b b' l: a=a' -> b=b' -> is_RInt f a b l -> is_RInt f a' b' l.
Proof. by intros <- <-. Qed.
Lemma RInt_ext' (f: R->R) a a' b b': a=a' -> b=b' -> RInt f a b = RInt f a' b'.
Proof. by intros <- <-. Qed.

Lemma Rdiv_r (a b c: R): c<>0 -> c*a = b -> a = b/c.
Proof. intros ? <-. by simpl; field. Qed.

Lemma RInt_lin (f: R->R) a b u v:
  u<>0 ->
  ex_RInt f (u * a + v) (u * b + v) ->
  RInt (fun x => f (u*x+v)) a b = RInt f (u*a+v) (u*b+v) / u.
Proof.
  intros U H. apply Rdiv_r=>//. etransitivity.
  symmetry; apply: RInt_scal =>//.
  apply ex_RInt_comp_lin in H.
  apply (ex_RInt_scal _ _ _ (/u)) in H.
  eapply ex_RInt_ext. 2: apply H. rewrite/scal/=/mult/= => x _. by field. 
  by rewrite RInt_comp_lin.
Qed.  

Definition rescale_ops {N: NBH} (BO: BasisOps) (A C: II): BasisOps := {|
  BI := rescale_ops_on BI A C;
  BF := rescale_ops_on BF (I2F A) (I2F C);
|}.

Section s.
 Context {N: NBH} {BO: BasisOps} (B: Basis BO) (D: Domain).

 Notation a := dlo.
 Notation c := dhi.
 Notation hiloca := ((hi-lo) / (c-a)).
 Let g (y: R) := lo + (y-a) * hiloca.            (* g: [a;b] -> [lo;hi] *)
 Let rTT n y := TT n (g y).
 Let lohi: lo < hi := lohi. 
 Let ac: a < c := dlohi. 

 Lemma r_eval: forall p y,
     eval rTT p y = eval TT p (g y).
 Proof.
   intros. rewrite /eval.
   generalize O. elim p =>[|?? IHp] n//=. by rewrite IHp. 
 Qed.

 Local Obligation Tactic := auto.
 Program Definition rescale: Basis (rescale_ops BO dlo dhi) := {|
   TT := rTT;
   BR := rescale_ops_on BR a c;
 |}.
 Next Obligation. by move=>p x/=; rewrite evalE r_eval /g. Qed. 
 Next Obligation. 
   move=> n x.
   apply (continuity_pt_comp g (TT n)).
   apply continuity_pt_plus.
   by apply continuity_pt_const.
   apply continuity_pt_mult. 
   apply continuity_pt_minus. apply continuity_pt_id.
   by apply continuity_pt_const.
   by apply continuity_pt_const.
   apply basis_cont.
 Qed.
 Next Obligation. intros. rewrite 3!r_eval. apply eval_mul. Qed.
 Next Obligation. intros. rewrite r_eval. apply eval_one. Qed.
 Next Obligation.
   intros. rewrite r_eval /= eval_add 2!eval_scal eval_id eval_one /g/hiloca /=.
   field. lra.
 Qed.
 Next Obligation.
   generalize eval_range. rewrite /dom/=.
   case brange=>[mM H p x Hx|_]//.
   rewrite r_eval. apply H. split; rewrite /g/=.
   rewrite Rplus_comm -Rle_minus_l Rminus_eq_0 -Rmult_assoc /=.
   apply Rdiv_le_0_compat.
   apply Rmult_le_pos; lra. lra. 
   rewrite Rplus_comm -Rle_minus_r /Rdiv -Rmult_assoc Rle_div_l/=. 2: lra.
   rewrite Rmult_comm.
   apply Rmult_le_compat; lra.
 Qed.
 Next Obligation.
   intros p i j. 
   set (v := lo - a * hiloca: R).
   rewrite /= integrateE /=.
   symmetry. erewrite RInt_ext; last first. intros.
   rewrite r_eval /g.
   replace (_+_) with (hiloca*x + v). 2: rewrite/v/=; ring. reflexivity.
   rewrite RInt_lin. 3: eexists; apply integrateE'. (* only place where we need integrateE' *)
   set (e:=RInt _ _ _). replace (RInt _ _ _) with e. rewrite /=. field; lra.
   unfold e. f_equal; rewrite /g/v/=; field; lra.
   apply Rmult_integral_contrapositive; (split; last apply Rinv_neq_0_compat);
     rewrite /=; lra.
 Qed.
 Next Obligation. apply rdlo. Qed.
 Next Obligation. apply rdhi. Qed.
 Next Obligation. intros=>/=. by apply rbmul. Qed.
 Next Obligation. intros=>/=. by apply rbone. Qed.
 Next Obligation. 
   apply rsadd; apply rsscal; try rel.
   apply rbid.
   apply rbone.
 Qed.
 Next Obligation. cbn. rel. Qed.
 Next Obligation. cbn. rel. Qed.
 Next Obligation. cbn. apply rbrange. Qed.
End s.
