(** * Operations on monomial basis (to obtain Taylor models) *)

Require Import vectorspace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition M k x := x^k.

(** naive evaluation (defined in vectorspace) *)
Notation eval_ := (eval_ M).
Notation eval := (eval M).


(** ** continuity/derivability properties *)

Lemma M_cont n x : continuity_pt (M n) x.
Proof.
  induction n as [ | n IHn].
+ now apply continuity_const.
+ unfold M; simpl; apply continuity_pt_mult.
  unfold continuity_pt; unfold continue_in; unfold limit1_in; unfold limit_in.
  now intros eps Heps; exists eps; split; first apply Heps; intros t.
  apply IHn.
Qed.
Definition eval_cont := eval_cont_basis M_cont.
Definition eval_ex_RInt := eval_ex_RInt M_cont.


Lemma M_ex_derive n x : ex_derive (M n) x.
Proof. apply ex_derive_pow; apply ex_derive_id. Qed.

Lemma M_Derive n x : Derive (M n.+1) x = INR n.+1 * M n x.
Proof.
  rewrite /M Derive_pow; last apply ex_derive_id.
  rewrite Derive_id /=; ring.
Qed.

Lemma eval_ex_derive_ P n x : ex_derive (eval_ n P) x.
Proof.
  elim: P n => [ | a P IHP] n /=.
+ apply ex_derive_const.
+ apply ex_derive_plus with (g:=eval_ n.+1 P); last apply IHP.
  apply ex_derive_mult; [apply ex_derive_const | apply M_ex_derive].
Qed.

Lemma eval_ex_derive P x : ex_derive (eval P) x.
Proof. apply eval_ex_derive_. Qed.


(** ** definition of the operations *)

(** linear time evaluation (Hörner) *)

Fixpoint eval' (R: Ops0) (P: list R) (x: R): R :=
  match P with
  | [] => 0
  | a::Q => a + x * eval' Q x
  end. 
Lemma evalR P x: eval' P x = eval P x.
Proof.
  assert(H: forall n, eval_ n P x = eval' P x * x ^ n).
  induction P as [|a Q IH]; intro; simpl; unfold M; rewrite ?IH; simpl; ring.
  unfold eval. rewrite H. simpl. lra. (* BUG: ring fails *)
Qed.


Section r.
 Context {C: Ops0}.
 Notation poly := (list C).

 Definition sone: poly := [1].
 
 Definition scst a: poly := [a].
 
 Fixpoint Xk (k: nat): poly :=
   match k with
   | O => [1]
   | S k => 0::Xk k
   end.
  
 (** multiplication *)
 Fixpoint smul (P Q: poly): poly :=
   match P with
   | [] => []
   | a::P => sadd (sscal a Q) (0::smul P Q)
   end.

 (** identity (X) *)
 Definition sid: poly := [0;1].
 
 (** composition *)
 Fixpoint comp (P Q: poly): poly :=
   match P with
   | [] => []
   | a::P => sadd (scst a) (smul (comp P Q) Q)
   end.

End r.

Section r'.
 Context {C: Ops1}.
 Notation poly := (list C).

 (** primitive *)
 Fixpoint prim_ n (P: poly) :=
   match P with
   | [] => []
   | x::P => x//n :: prim_ (S n) P
   end.

 Definition prim P := 0::prim_ 1 P.

End r'.


(** interpolation (not implemented for monomial basis, for now) *)
Parameter interpolate: forall {C: Ops1}, Z -> (C -> C) -> list C.


(** ** correctness of the operations on reals  *)

Lemma eval_cst a (x: R): eval (scst a) x = a.
Proof. compute. ring. Qed.

Lemma eval_one (x: R): eval sone x = 1.
Proof. compute. ring. Qed.

Lemma eval_id (x: R): eval sid x = x.
Proof. compute. ring. Qed.

Lemma eval_mul: forall P Q (x: R), eval (smul P Q) x = eval P x * eval Q x.
Proof.
  intros. rewrite -!evalR. revert Q x. 
  induction P as [|a P IH]; intros Q x; simpl. ring.
  rewrite !evalR eval_add eval_scal -!evalR.
  rewrite /=IH/=; ring. 
Qed.

Lemma eval_comp: forall P Q (x: R), eval (comp P Q) x = eval P (eval Q x).
Proof.
  intros. rewrite -!evalR. revert Q x. 
  induction P as [|a P IH]; intros Q x; simpl. reflexivity. 
  rewrite !evalR eval_add eval_mul eval_cst -!evalR.
  rewrite /=IH/=; ring. 
Qed.

Lemma eval_prim_ n p x : Derive (eval_ n.+1 (prim_ n.+1 p)) x = eval_ n p x.
Proof.
  elim: p n => [ | a p IHp] /= n. 
+ by rewrite Derive_const.
+ rewrite Derive_plus; last apply eval_ex_derive_.
  rewrite Derive_scal IHp M_Derive.
  fold (Z.of_nat (n.+1)). rewrite -INR_IZR_INZ. simpl; field.
  by apply (not_0_INR n.+1).
  apply ex_derive_scal; apply (M_ex_derive n.+1).
Qed.

Lemma eval_prim_Derive p x : Derive (eval (prim p)) x = eval p x.
Proof.
  rewrite /prim /eval /=.
  rewrite Derive_plus; last apply eval_ex_derive_; last apply ex_derive_const.
  rewrite Derive_const eval_prim_; ring.
Qed.

Lemma eval_prim p a b : eval (prim p) b - eval (prim p) a = RInt (eval p) a b.
Proof.
  rewrite -(RInt_ext (Derive (eval (prim p)))); last by move => t _; rewrite eval_prim_Derive.
  rewrite RInt_Derive. by []. 
* move => t _; apply eval_ex_derive.
* move => t _; apply continuous_ext with (f:= eval p); first by move => u; rewrite eval_prim_Derive.
  apply continuity_pt_filterlim; apply eval_cont.
Qed.

Lemma eval_prim' p a b : is_RInt (eval p) a b (eval (prim p) b - eval (prim p) a).
Proof. rewrite eval_prim; apply (RInt_correct (eval p)); apply eval_ex_RInt. Qed.

(** ** parametricity of the operations  *)

Section s.
 Context {R S: Ops0}.
 Variable T: Rel0 R S.
 Notation sT := (list_rel T).
 Lemma rsmul: forall x y, sT x y -> forall x' y', sT x' y' -> sT (smul x x') (smul y y').
 Proof. induction 1; simpl; rel. Qed.
 Lemma rsone: sT sone sone.
 Proof. simpl. unfold sone. rel. Qed.
 Lemma rsid: sT sid sid.
 Proof. simpl. unfold sid. rel. Qed.
 Lemma rscst: forall a b, rel T a b -> sT (scst a) (scst b).
 Proof. unfold scst. rel. Qed.
 Lemma rXk k: sT (Xk k) (Xk k).
 Proof. induction k; simpl; rel. Qed.
 Hint Resolve rsmul rscst: rel.
 Lemma rcomp: forall x y, sT x y -> forall x' y', sT x' y' -> sT (comp x x') (comp y y').
 Proof. induction 1; simpl; rel. Qed.
 Lemma reval: forall P Q, sT P Q -> forall x y, T x y -> T (eval' P x) (eval' Q y).
 Proof. induction 1; simpl; rel. Qed.
End s.

Section s'.
 Context {R S: Ops1}.
 Variable T: Rel1 R S.
 Notation sT := (list_rel T).
 Lemma rprim_: forall x y, sT x y -> forall n, sT (prim_ n x) (prim_ n y).
 Proof. induction 1; simpl; rel. Qed.
 Hint Resolve rprim_ reval: rel.
 Lemma rprim: forall x y, sT x y -> sT (prim x) (prim y).
 Proof. intros. constructor; rel. Qed.
End s'.

(** packing everything together, we get a basis *)

Definition basis_ops_on (C: Ops1) (lo hi: C): BasisOps_on C := {|
  vectorspace.lo := lo;
  vectorspace.hi := hi;
  vectorspace.bmul := smul;
  vectorspace.bone := sone;
  vectorspace.bid := sid;
  vectorspace.bprim := prim;
  vectorspace.beval := @eval' C;
  vectorspace.brange := None;
  vectorspace.interpolate := interpolate
|}.

Definition basis_ops {N: NBH} (lo hi: II): BasisOps := {|
  BI := basis_ops_on lo hi;
  BF := basis_ops_on (I2F lo) (I2F hi);
|}.

Program Definition basis {N: NBH} (D: Domain):
  Basis (basis_ops dlo dhi) := {|
  TT := M;
  BR := basis_ops_on dlo dhi;
  vectorspace.lohi := dlohi;
  vectorspace.evalE := evalR;
  vectorspace.eval_cont := eval_cont;
  vectorspace.eval_mul := eval_mul;
  vectorspace.eval_one := eval_one;
  vectorspace.eval_id := eval_id;
  vectorspace.eval_prim' := eval_prim';
  vectorspace.eval_prim := eval_prim;
  vectorspace.eval_range := I;
  vectorspace.rlo := rdlo;
  vectorspace.rhi := rdhi;
  vectorspace.rbmul := @rsmul _ _ (contains (NBH:=N));
  vectorspace.rbone := @rsone _ _ _;
  vectorspace.rbid := @rsid _ _ _;
  vectorspace.rbprim := @rprim _ _ _;
  vectorspace.rbeval := @reval _ _ _;
  vectorspace.rbrange := I;
|}.
