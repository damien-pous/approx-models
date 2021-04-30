(** * Rescaling operation on bases *)

Require Import vectorspace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section r.
 Variable C: Ops1.
 Variable D: Domain_on C.
 Variable B: BasisOps_on C.
 Variables lo' hi': C.          (* B *)
 Let a: C := lo.                (* D *)
 Let b: C := hi.                (* D *)
 Let lo: C := lo'.              (* B *)
 Let hi: C := hi'.              (* B *)
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

 Let a: II := @lo _ (@DI N D).
 Let b: II := @hi _ (@DI N D).
 Let a': R := @lo _ (@DR N D).
 Let b': R := @hi _ (@DR N D).
 Let lo': R := @lo _ (@DR N bdom).
 Let hi': R := @hi _ (@DR N bdom).
 Let lo: II := @lo _ (@DI N bdom).
 Let hi: II := @hi _ (@DI N bdom).
 Let bahilo: II := (b-a) / (hi-lo). 
 Let hiloba: II := (hi-lo) / (b-a).
 Let f (x: II) := lo + (x-a) * hiloba.
 Let g (y: II) := a + (y-lo) * bahilo.
 Let r_id: list II := sscal bahilo bid + sscal (a-lo*bahilo) 1.
 Let r_beval (p: list II) (x: II) := beval p (f x).
 Let r_evalR (p: list R) (x: R) := beval p (lo' + (x-a') * ((hi'-lo')/(b'-a'))).
 Let r_interpolate n h := interpolate n (fun x => h (g x)).
 Let r_prim (p: list II) := sscal bahilo (bprim p). 
 Let r_M n x := TT n (lo' + (x-a')*((hi'-lo')/(b'-a'))).
 Let ab: a' < b' := lohi. 
 Let lohi: lo' < hi' := lohi. 

 Lemma r_eval: forall p x,
     vectorspace.eval r_M p x = vectorspace.eval TT p (lo' + (x-a')*((hi'-lo')/(b'-a'))).
 Proof.
   intros. rewrite /vectorspace.eval.
   generalize O. elim p =>[|?? IHp] n//=. by rewrite IHp.
 Qed.

 Program Definition to: Basis := {|
   TT := r_M;
   bdom := D;
   BR := rescale_on DR BR lo' hi';
   BI := rescale_on DI BI lo hi;
   BF := rescale_on DF BF (@interfaces.lo _ (@DF N bdom)) (@interfaces.hi _ (@DF N bdom));
 |}.
 Next Obligation. by rewrite evalE r_eval. Qed. 
 Next Obligation. 
   eapply continuity_pt_ext. intro. rewrite r_eval. reflexivity.
   apply (continuity_pt_comp (fun x0 => (lo' + (x0 - a') * ((hi' - lo') / (b' - a')))) (vectorspace.eval TT p)). 
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
   unfold hi', lo', a', b' in *. field. lra.
 Qed.
 Next Obligation.
   set (u := ((hi'-lo')/(b'-a')): R).
   set (v := lo'- a' * u : R).
   rewrite 2!eval_scal/= -Rmult_minus_distr_l.
   eapply is_RInt_ext; last first.
   apply: is_RInt_scal. apply: (is_RInt_comp_lin _ u v).
   rewrite 2!r_eval/=. eapply is_RInt_ext'; last apply eval_prim'; rewrite /v/u/=; field; lra.
   intros=>/=. rewrite r_eval /scal/=/mult/v/u/=.
   rewrite -Rmult_assoc.
   unfold hi', lo', a', b' in *.
   replace (_/_*_) with R1 by (rewrite /=; field; lra).
   rewrite Rmult_1_l. f_equal. field; lra. 
 Qed.
 Next Obligation.
   set (u := ((hi'-lo')/(b'-a')): R).
   set (v := lo'- a' * u : R).
   rewrite 2!eval_scal/= -Rmult_minus_distr_l 2!r_eval eval_prim /=.
   symmetry. erewrite RInt_ext; last first. intros.
   rewrite r_eval.
   replace (_+_) with (u*x + (lo' - a'*u)). 2: rewrite /u/=; field; lra. reflexivity.
   rewrite RInt_lin. 3: eexists; apply eval_prim'.
   set (e:=RInt _ _ _). replace (RInt _ _ _) with e. rewrite /u/=.
   unfold hi', lo', a', b' in *.
   field; lra.
   unfold e. f_equal; rewrite /u/=; field; lra.
   apply Rmult_integral_contrapositive; (split; last apply Rinv_neq_0_compat);
     rewrite /=; lra.
 Qed.
 Next Obligation.
   generalize eval_range; simpl. case brange=>[? H|_]//.
   rewrite /dom/=; intros. rewrite r_eval/=. apply H.
   generalize lohi. generalize ab. rewrite /dom/=. split. 
   rewrite Rplus_comm -Rle_minus_l Rminus_eq_0 -Rmult_assoc /=.
   apply Rdiv_le_0_compat.
   unfold hi', lo', a', b' in *.
   apply Rmult_le_pos; lra. lra. 
   rewrite Rplus_comm -Rle_minus_r /Rdiv -Rmult_assoc Rle_div_l. 2: lra.
   rewrite Rmult_comm.
   unfold hi', lo', a', b' in *.
   apply Rmult_le_compat; lra.
 Qed.
 Next Obligation. now apply rbmul. Qed.
 Next Obligation. now apply rbone. Qed.
 Next Obligation.
   apply rsadd; apply rsscal; try rel.
   apply rdiv; try rel. apply rsub. apply rhi. apply rlo. 
   apply rbid.
   apply rsub; try rel. 
   apply rmul; try rel. apply rlo. 
   apply rdiv; try rel. apply rsub. apply rhi. apply rlo. 
   apply rbone.
 Qed.
 Next Obligation.
   apply rsscal.
   apply rdiv; try rel. apply rsub. apply rhi. apply rlo. 
   by apply rbprim.
 Qed.
 Next Obligation.
   apply rbeval=>//.
   apply radd. apply rlo.
   apply rmul; try rel. 
   apply rdiv; try rel.
   apply rsub. apply rhi. apply rlo. 
 Qed.
 Next Obligation. apply rbrange. Qed.
End s.
