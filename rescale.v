(** * Rescaling operation on bases *)

Require Import vectorspace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section r.
 Variable D: Domain.
 Variable C: Ops1.
 Variable B: BasisOps_on C.
 Let a: C := dlo.
 Let b: C := dhi.
 Let bahilo: C := (b-a) / (hi-lo). 
 Let hiloba: C := (hi-lo) / (b-a).
 Let f (x: C) := lo + (x-a) * hiloba. (* [a;b]->[lo;hi] *)
 Let g (y: C) := a + (y-lo) * bahilo. (* [lo;hi]->[a;b] *)
 Let r_id: list C := sscal bahilo bid + sscal (a-lo*bahilo) bone.
 Let r_eval (p: list C) (x: C) := beval p (f x).
 Let r_interpolate n h := interpolate n (fun x => h (g x)).
 Let r_prim (p: list C): list C := sscal bahilo (bprim p).
 Definition rescale_on: BasisOps_on C :=
   {|
     bmul := bmul;
     bone := bone;
     bid := r_id;
     bprim := r_prim;
     beval := r_eval;
     lo:=a;
     hi:=b;
     brange:=brange;
     interpolate:=r_interpolate;
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

Section s.
 Context {N: NBH} (D: Domain) (B: Basis).

 Let a: II := dlo.
 Let b: II := dhi.
 Let bahilo: II := (b-a) / (hi-lo). 
 Let hiloba: II := (hi-lo) / (b-a).
 Let f (x: II) := lo + (x-a) * hiloba.
 Let g (y: II) := a + (y-lo) * bahilo.
 Let r_id: list II := sscal bahilo bid + sscal (a-lo*bahilo) 1.
 Let r_beval (p: list II) (x: II) := beval p (f x).
 Let r_evalR (p: list R) (x: R) := beval p (lo + (x-dlo) * ((hi-lo)/(dhi-dlo))).
 Let r_interpolate n h := interpolate n (fun x => h (g x)).
 Let r_prim (p: list II) := sscal bahilo (bprim p). 
 Let r_M n x := TT n (lo + (x-dlo)*((hi-lo)/(dhi-dlo))).
 Let lohi: lo < hi := lohi. 
 Let dlohi: dlo < dhi := dlohi. 

 Lemma r_eval: forall p x,
     vectorspace.eval r_M p x = vectorspace.eval TT p (lo + (x-dlo)*((hi-lo)/(dhi-dlo))).
 Proof.
   intros. rewrite /vectorspace.eval.
   generalize O. elim p =>[|?? IHp] n//=. by rewrite IHp.
 Qed.

 Program Definition to: Basis := {|
   TT := r_M;
   BR := rescale_on D BR;
   BI := rescale_on D BI;
   BF := rescale_on D BF;
 |}.
 Next Obligation. by rewrite evalE r_eval. Qed.
 Next Obligation. 
   eapply continuity_pt_ext. intro. rewrite r_eval. reflexivity.
   apply (continuity_pt_comp (fun x0 => (lo + (x0 - dlo) * ((hi - lo) / (dhi - dlo)))) (vectorspace.eval TT p)). 
   apply continuity_pt_plus.
   by apply continuity_pt_const.
   apply continuity_pt_mult. 
   apply continuity_pt_minus. apply continuity_pt_id.
   by apply continuity_pt_const.
   by apply continuity_pt_const.
   apply eval_cont.
 Qed.
 Next Obligation. rewrite 3!r_eval. apply eval_mul. Qed.
 Next Obligation. rewrite r_eval. apply eval_one. Qed.
 Next Obligation.
   rewrite r_eval /= eval_add 2!eval_scal eval_id eval_one /=.
   field. lra.
 Qed.
 Next Obligation.
   set (u := ((hi-lo)/(dhi-dlo)): R).
   set (v := lo- dlo * u : R).
   rewrite 2!eval_scal/= -Rmult_minus_distr_l.
   eapply is_RInt_ext; last first.
   apply: is_RInt_scal. apply: (is_RInt_comp_lin _ u v).
   rewrite 2!r_eval/=. eapply is_RInt_ext'; last apply eval_prim'; rewrite /v/u/=; field; lra.
   intros=>/=. rewrite r_eval /scal/=/mult/v/u/=.
   rewrite -Rmult_assoc. replace (_/_*_) with R1 by (rewrite /=; field; lra).
   rewrite Rmult_1_l. f_equal. field; lra. 
 Qed.
 Next Obligation.
   set (u := ((hi-lo)/(dhi-dlo)): R).
   set (v := lo- dlo * u : R).
   rewrite 2!eval_scal/= -Rmult_minus_distr_l 2!r_eval eval_prim /=.
   symmetry. erewrite RInt_ext; last first. intros.
   rewrite r_eval.
   replace (_+_) with (u*x + (lo - dlo*u)). 2: rewrite /u/=; field; lra. reflexivity.
   rewrite RInt_lin. 3: eexists; apply eval_prim'.
   set (e:=RInt _ _ _). replace (RInt _ _ _) with e. rewrite /u/=. field; lra.
   unfold e. f_equal; rewrite /u/=; field; lra.
   apply Rmult_integral_contrapositive; (split; last apply Rinv_neq_0_compat);
     rewrite /=; lra.
 Qed.
 Next Obligation.
   generalize eval_range; simpl. case brange=>[? H|_]//.
   rewrite /dom/=; intros. rewrite r_eval/=. apply H.
   generalize lohi. generalize dlohi. rewrite /dom/=. split. 
   rewrite Rplus_comm -Rle_minus_l Rminus_eq_0 -Rmult_assoc /=.
   apply Rdiv_le_0_compat. apply Rmult_le_pos; lra. lra. 
   rewrite Rplus_comm -Rle_minus_r /Rdiv -Rmult_assoc Rle_div_l. 2: lra.
   rewrite Rmult_comm. apply Rmult_le_compat; lra.
 Qed.
 Next Obligation. apply rdlo. Qed.
 Next Obligation. apply rdhi. Qed.
 Next Obligation. now apply rbmul. Qed.
 Next Obligation. now apply rbone. Qed.
 Next Obligation.
   apply rsadd; apply rsscal; try rel. apply rbid. apply rbone.
 Qed.
 Next Obligation.
   apply rsscal. rel. by apply rbprim.
 Qed.
 Next Obligation. rel. Qed.
 Next Obligation. apply rbrange. Qed.
 
End s.
