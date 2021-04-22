(** * Rescaling operation on bases *)

Require Import vectorspace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section r.
 Variable D: Domain.
 Section s. 
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
 End s.
 Context {N: NBH} (B: BasisOps).
 Definition rescale: BasisOps :=
   {|
     BR := rescale_on BR;
     BI := rescale_on BI;
     BF := rescale_on BF;
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

Definition rescale_T {N: NBH} {B: BasisOps} (D: Domain) (T: nat -> R -> R) n x :=
  T n (lo + (x-dlo)*((hi-lo)/(dhi-dlo))).
   
Instance valid {N: NBH} {B: BasisOps} (D: Domain) {T} (HB: ValidBasisOps T B):
  ValidBasisOps (rescale_T D T) (rescale D B).
Proof.
 set a: II := dlo.
 set b: II := dhi.
 set bahilo: II := (b-a) / (hi-lo). 
 set hiloba: II := (hi-lo) / (b-a).
 set (f (x: II) := lo + (x-a) * hiloba).
 set (g (y: II) := a + (y-lo) * bahilo).
 set r_id: list II := sscal bahilo bid + sscal (a-lo*bahilo) 1.
 set (r_beval (p: list II) (x: II) := beval p (f x)).
 set (r_evalR (p: list R) (x: R) := beval p (lo + (x-dlo) * ((hi-lo)/(dhi-dlo)))).
 set (r_interpolate n h := interpolate n (fun x => h (g x))).
 set (r_prim (p: list II) := sscal bahilo (bprim p)). 
 set (r_M := rescale_T D T). 
 assert(r_eval: forall p x,
           vectorspace.eval r_M p x = vectorspace.eval T p (lo + (x-dlo)*((hi-lo)/(dhi-dlo)))).
   intros. rewrite /vectorspace.eval.
   generalize O. elim p =>[|?? IHp] n//=. by rewrite IHp.
 generalize lohi dlohi => lohi' dlohi'.
 constructor =>//; try solve [apply D | apply HB].
 - intros. simpl. by rewrite evalE. 
 - intros. simpl. 
   eapply continuity_pt_ext. intro. rewrite r_eval. reflexivity.
   apply (continuity_pt_comp (fun x0 => (lo + (x0 - dlo) * ((hi - lo) / (dhi - dlo)))) (vectorspace.eval T p)). 
   apply continuity_pt_plus.
   by apply continuity_pt_const.
   apply continuity_pt_mult. 
   apply continuity_pt_minus. apply continuity_pt_id.
   by apply continuity_pt_const.
   by apply continuity_pt_const.
   apply eval_cont.
 - intros. rewrite 3!r_eval. apply (@eval_mul _ _ _ HB).
 - intros. rewrite r_eval. apply (@eval_one _ _ _ HB).
 - intros. rewrite r_eval /= eval_add 2!eval_scal eval_id eval_one /=.
   field. lra. 
 - simpl. intros.
   set (u := ((hi-lo)/(dhi-dlo)): R).
   set (v := lo- dlo * u : R).
   rewrite 2!eval_scal/= -Rmult_minus_distr_l.
   eapply is_RInt_ext; last first.
   apply: is_RInt_scal. apply: (is_RInt_comp_lin _ u v).
   rewrite 2!r_eval/=. eapply is_RInt_ext'; last apply eval_prim'; rewrite /v/u/=; field; lra.
   intros=>/=. rewrite r_eval /scal/=/mult/v/u/=.
   rewrite -Rmult_assoc. replace (_/_*_) with R1 by (rewrite /=; field; lra).
   rewrite Rmult_1_l. f_equal. field; lra. 
 - intros =>/=. 
   set (u := ((hi-lo)/(dhi-dlo)): R).
   set (v := lo- dlo * u : R).
   rewrite 2!eval_scal/= -Rmult_minus_distr_l 2!r_eval eval_prim /=.
   symmetry. erewrite RInt_ext; last first. intros. rewrite r_eval.
   replace (_+_) with (u*x + (lo - dlo*u)). 2: rewrite /u/=; field; lra. reflexivity.
   rewrite RInt_lin. 3: eexists; apply eval_prim'.
   set (e:=RInt _ _ _). replace (RInt _ _ _) with e. rewrite /u/=. field; lra.
   unfold e. f_equal; rewrite /u/=; field; lra.
   apply Rmult_integral_contrapositive; (split; last apply Rinv_neq_0_compat);
     rewrite /=; lra.
 - generalize eval_range; simpl. case brange=>[? H|_]//.
   rewrite /dom/=; intros. rewrite r_eval/=. apply H.
   generalize lohi. generalize dlohi. rewrite /dom/=. split. 
   rewrite Rplus_comm -Rle_minus_l Rminus_eq_0 -Rmult_assoc /=.
   apply Rdiv_le_0_compat. apply Rmult_le_pos; lra. lra. 
   rewrite Rplus_comm -Rle_minus_r /Rdiv -Rmult_assoc Rle_div_l. 2: lra.
   rewrite Rmult_comm. apply Rmult_le_compat; lra.
 - apply rsadd; apply rsscal. apply rdiv; apply rsub; (apply D || apply HB). apply rbid.
   apply rsub. apply rdlo. apply rmul. apply rlo. apply rdiv; apply rsub; (apply D || apply HB).
 - apply rbone.
 - intros. apply rsscal. apply rdiv; apply rsub; (apply D || apply HB).
     by apply rbprim.
 - intros. simpl. apply rbeval=>//. 
   apply radd. apply rlo. apply rmul. apply rsub=>//; apply rdlo.
   apply rdiv; apply rsub; (apply D || apply HB).
Qed.
