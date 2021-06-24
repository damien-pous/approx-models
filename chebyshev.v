(** * Chebyshev polynomials and arithmetic of Chebyshev basis *)

Require Import String.
Require Import vectorspace rescale utils.
Require Import Reals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** ** Chebyshev polynomials and their key properties *)
Fixpoint T n x :=
  match n with
  | 0 => 1
  | 1 => x
  | S (S n as m) => 2*x*T m x - T n x
  end.

Lemma TSS n x : T (n.+2) x = 2*x*T (n.+1) x - T n x.
Proof. reflexivity. Qed.

Lemma T0 x: T 0 x = 1.
Proof. reflexivity. Qed.

Lemma T1 x: T 1 x = x.
Proof. reflexivity. Qed.

Lemma T2 x: T 2 x = 2 * x^2 - 1.
Proof. simpl. ring. Qed.

Opaque T.

Lemma nat2_ind (P: nat -> Prop) :
  P 0%nat -> P 1%nat -> (forall n, P n -> P (n.+1) -> P (n.+2)) -> forall n, P n.
Proof.
  intros ???. cut (forall n, P n /\ P (S n)). firstorder.
  induction n; firstorder. 
Qed.  

Lemma Tprod: forall n m (x: R),
    (n<=m)%nat -> T n x * T m x = (T (m+n) x + T (m-n) x) / 2.
Proof.
  intros n m x H. induction n as [| |n IH1 IH2] using nat2_ind.
  - rewrite T0 -plus_n_O -minus_n_O /=; field.
  - rewrite T1. destruct m as [|m]. lia.
    rewrite Nat.sub_succ Nat.sub_0_r Nat.add_1_r TSS /=. field.
  - rewrite TSS /=. ring_simplify.
    rewrite !Rmult_assoc IH1. 2:lia. rewrite IH2. 2: lia.
    replace (m-n)%nat with (m-n.+2).+2 by lia.
    rewrite TSS.
    replace (m-n.+2).+1 with (m-n.+1)%nat by lia.
    rewrite !Nat.add_succ_r !TSS /=. field.
Qed.

Corollary Tsqr: forall n x, T n x ^ 2 = (T (n+n) x + 1)/2.
Proof. intros. rewrite (pow_add _ 1 1) pow_1 Tprod // Nat.sub_diag //. Qed. 

(** relationship between Chebyshev polynomials and trigonometric functions *)
Lemma T_cos n t : T n (cos t) = cos (INR n * t).
Proof.
  induction n as [| | n IH1 IH2] using nat2_ind.
+ by rewrite /= T0 Rmult_0_l cos_0.
+ by rewrite /= Rmult_1_l T1.
+ rewrite TSS IH1 IH2.
  replace (cos (INR n.+2 * t)) with ((cos (INR n.+2 * t) + cos (INR n * t)) - cos (INR n * t)).
    2: by rewrite /=; ring.
  rewrite !INRS /= Rtrigo1.form1 -!INRS.
  replace ((INR n.+2 * t - INR n * t) / 2)%R with t. 2: rewrite !INRS; field.
  replace ((INR n.+2 * t + INR n * t) / 2)%R with (INR n.+1 * t)%R. 2: rewrite !INRS/=; field.
  reflexivity. 
Qed.

Lemma cos_range (x : R) : -1 <= x <= 1 -> exists t, 0 <= t <= PI /\ cos t = x.
Proof.
  intro Hx. destruct (IVT_gen _ 0 PI x continuity_cos) as [t Ht].
  rewrite cos_0 cos_PI. setoid_rewrite Rmin_r. setoid_rewrite <-Rmax_l . assumption.
  pose proof PI_RGT_0.
  replace (Rmin _ _) with 0%R in Ht by (rewrite Rmin_left//; lra).
  replace (Rmax _ _) with PI in Ht by (rewrite Rmax_right//; lra).
  by exists t. 
Qed.

(** as a corollary, their range is [[-1;1]] on [[-1;1]] *)
Corollary T_range n x : -1 <= x <= 1 -> -1 <= T n x <= 1.
Proof.
  intro Hx; destruct (cos_range Hx) as [t [_ Ht]].
  rewrite -Ht T_cos.
  apply COS_bound.
Qed.


(** Chebyshev polynomials are continuous at every point *)
Lemma T_cont n x : continuity_pt (T n) x.
Proof.
  induction n as [| | n IH1 IH2] using nat2_ind.
  + by apply continuity_pt_const.
  + by apply continuity_pt_id.
  + eapply continuity_pt_ext. by intro; rewrite TSS.
    apply continuity_pt_minus; trivial.
    apply continuity_pt_mult; trivial.
    apply continuity_pt_scal, continuity_pt_id.
Qed.

(** Chebyshev polynomials are derivable at every point *)
Lemma T_ex_derive n x : ex_derive (T n) x.
Proof.
  induction n as [| | n IH1 IH2] using nat2_ind.
  + eapply ex_derive_ext; first by intro; rewrite T0.
    apply ex_derive_const.
  + apply ex_derive_id.
  + eapply ex_derive_ext. by intro; rewrite TSS.
    apply: ex_derive_minus; trivial.
    apply ex_derive_mult; trivial.
    apply ex_derive_scal, ex_derive_id.
Qed.

(** relations between Chebyshev polynomials and their derivatives  *)
Lemma T_Derive0 x : Derive (T 1) x = T 0 x.
Proof.
  rewrite (Derive_ext _ id). 2: apply T1.
  by rewrite Derive_id T0.
Qed.

Lemma T_Derive1 x : Derive (fun t => / INR 4 * T 2 t) x = T 1 x.
Proof.
  erewrite Derive_ext. 2: by intro; rewrite T2.
  rewrite T1 Derive_scal Derive_minus ?Derive_const ?Derive_scal ?Derive_pow ?Derive_id; 
    repeat auto_derive; trivial. 
  simpl. field.
Qed.

Lemma T_DeriveSS n x : Derive (fun t => / (INR ((n.+3)*2)) * T n.+3 t - / (INR ((n.+1)*2)) * T n.+1 t) x = T n.+2 x.
Proof.
  induction n as [| | n IH1 IH2] using nat2_ind.
+ erewrite Derive_ext; first last.
  by intro; rewrite !TSS !T0 !T1.
  rewrite T2 /=; apply is_derive_unique; auto_derive=>//; field.
+ erewrite Derive_ext; first last.
  by intro; rewrite !TSS !T0 !T1.
  rewrite TSS T2 T1 /=; apply is_derive_unique; auto_derive=>//; field.
+ set g := fun t => INR n.+4 / INR n.+5 * ((2*t) * (/ INR ((n.+4)*2) * T n.+4 t - / INR ((n.+2)*2) * T n.+2 t)
    - ( / INR ((n.+3)*2) * T n.+3 t - / INR ((n.+1)*2) * T n.+1 t)
    + / INR n.+2 * (/ INR ((n.+3)*2) * T n.+3 t - / INR ((n.+1)*2) * T n.+1 t)).
  have INR0 : INR 0 = 0 by [].
  have INR1 : 1%R = INR 1 by [].
  have INR2 : 2%R = INR 2 by [].
  Opaque INR.
  rewrite (Derive_ext _ g).
  rewrite Derive_scal Derive_plus /=; try auto_derive; repeat split; try apply T_ex_derive.
  rewrite Derive_scal IH1 Derive_minus ?IH1; try auto_derive; try repeat split; try apply T_ex_derive.
  rewrite Derive_mult ?Derive_scal ?Derive_id ?IH2; try auto_derive; try repeat split; try apply T_ex_derive.
* rewrite !INR1 !TSS !INRS !mult_INR !INRS !INR0 /=; field.
  rewrite -!INRS INR2 -!mult_INR INR1 -!plus_INR; repeat try split; apply not_0_INR; lia.
* intro; rewrite /g !TSS !INRS !mult_INR !INRS !INR0 /=; field.
  rewrite -!INRS INR2 -!mult_INR INR1 -!plus_INR; repeat try split; apply not_0_INR; lia.
  Transparent INR.
Qed.


(** naive evaluation (defined in vectorspace, not even Horner, and only for reals) 
    eval [a b c] x = a * T 0 x + b * T 1 x + c * T 2 x + 0
*)
Notation eval_ := (eval_ T).
Notation eval := (eval T).

(** derivability of evaluation *)

Lemma eval_ex_derive_ n P x: ex_derive (eval_ n P) x.
Proof. apply eval_ex_derive_basis_, T_ex_derive. Qed. 
Lemma eval_ex_derive P x: ex_derive (eval P) x.
Proof. apply eval_ex_derive_. Qed. 


(** ** operations on polynomials
    This time parametrised by a abstract set C of operations.
    Later, C will be instanciated with reals, floating points, and intervals.
 *)
Section ops.

 Context {C: Ops0}.

 (** constant *)
 Definition pcst a: list C := [a].

 (** one *)
 Definition pone: list C := [1].

 (** identity (X) *)
 Definition pid: list C := [0;1].

 (** optimised cons operations, from primitive and multiplication *)
 Definition cons0 (p: list C) := match p with [] => p | _=>0::p end.
 
 Definition cons00 (p: list C) :=
   match p with [] => p | _=>0::0::p end.
 
 (** multiplication *)
 Fixpoint mul_minus (p q: list C): list C :=
   match p,q with
   | [],_ | _,[] => []
   | a :: p', b :: q' => sadd (a*b :: (sadd (sscal a q') (sscal b p'))) (mul_minus p' q')
   end.
 
 Fixpoint mul_plus (p q: list C): list C :=
   match p,q with
   | [],_ | _,[] => []
   | a :: p', b :: q' => sadd (a*b :: (sadd (sscal a q') (sscal b p'))) (cons00 (mul_plus p' q'))
   end.
 
 Definition pmul (p q: list C): list C :=
   sdivZ 2 (sadd (mul_minus p q) (mul_plus p q)).

 (** primitive  *)
 Fixpoint prim_ (n : nat) (p : list C) : list C :=
  match p with
    | [] => []
    | a :: q =>
      match n with
        | 0 => sadd [ 0; a] (prim_ 1 q)
        | 1 => cons0 (sadd [0; a // 4] (prim_ 2 q))
        | (_.+1 as n').+1 => sadd [0 - a // (n'*2); 0; a // ((n.+1)*2)%nat]
                        (cons0 (prim_ n.+1 q))
      end
  end.
 Definition prim p := prim_ 0 p.

 (** linear time evaluation (Clenshaw) *)
 Fixpoint Clenshaw b c (P: list C) x :=
   match P with
   | [] => c - x*b
   | a::Q => Clenshaw c (a + mulZ 2 (x*c) - b) Q x 
   end.
 Definition eval' P x := Clenshaw 0 0 (rev P) x.
 (** recall: 
    - [eval'] is the efficient evaluation of a polynomial, available on R, F, I 
    - [eval]  is the inefficient yet mathematically simple evaluation of a polynomial, available only on R *)

 (** integration *)
 Definition integrate p a b :=
   let q := prim p in eval' q b - eval' q a. 
 
End ops.
 
(** domain *)
Definition lo {C: Ops1}: C := fromZ (-1).
Definition hi {C: Ops1}: C := 1.

(** range on [[-1;1]]
    since the [T n] have their range in [[-1;1]], it suffices to take the sum of the absolute values of   the coefficients. for the constant coefficient, we don't even have to take the absolute value.
 *)
Definition range_ {C: Ops1}: list C -> C := List.fold_right (fun a x => abs a + x) 0.
Definition range {C: Ops1} p: C*C :=
  match p with
  | [] => (0,0)
  | a :: q => let r := range_ q in (a-r,a+r)
  end.


(** ** correctness of the above operations, on R *)

Lemma eval_cst a (x: R): eval (pcst a) x = a.
Proof. compute. rewrite T0/=. ring. Qed.

Lemma eval_one (x: R): eval pone x = 1.
Proof. compute. rewrite T0/=. ring. Qed.

Lemma eval_id (x: R): eval pid x = x.
Proof. compute. rewrite T0 T1/=. ring. Qed.

Lemma eval_cons0_ n p (x: R): eval_ n (cons0 p) x = eval_ n.+1 p x.
Proof. destruct p=>//=. ring. Qed.
Lemma eval_cons00_ n p (x: R): eval_ n (cons00 p) x = eval_ n.+2 p x.
Proof. destruct p=>//=. ring. Qed.

Lemma Teval: forall p n m x,
  (n<=m)%nat -> T n x * eval_ m p x = (eval_ (m+n) p x + eval_ (m-n) p x)/2.
Proof.
  induction p as [|a p IH]; intros n m x H; simpl.
  - field.
  - ring_simplify. rewrite IH. 2: lia. 
    replace (_*T m x) with (a*(T n x * T m x)) by (simpl; ring). 
    rewrite  Tprod //. 
    replace (S m - n)%nat with (S (m-n)) by lia.
    rewrite Nat.add_succ_l /=. field. 
Qed.

Lemma eval_mul_: forall p q n x,
    eval_ n p x * eval_ n q x =
    (eval_ 0 (mul_minus p q) x + eval_ (n+n) (mul_plus p q) x)/2.
Proof.
  induction p as [|a p' IH]; intros [|b q'] n x; simpl; try field.
  rewrite !eval_add_/=; ring_simplify.
  rewrite IH !eval_add_ !eval_scal_ eval_cons00_ Tsqr /= Nat.add_succ_r. 
  rewrite 2!Rmult_assoc Teval. 2: lia. rewrite Teval. 2:lia. 
  replace (S n-n)%nat with 1%nat by lia.
  rewrite T0 Nat.add_succ_l /=. field. 
Qed.
Lemma eval_mul: forall P Q (x: R), eval (pmul P Q) x = eval P x * eval Q x.
Proof. intros. rewrite /eval eval_mul_ /pmul eval_divZ_ eval_add_//. Qed.




Lemma eval_app_: forall P Q (x: R) n, eval_ n (P ++ Q) x = eval_ n P x + eval_ (length P + n) Q x.
Proof.
  intros P; induction P as [|a P IH]; intros Q x n.
  - compute; ring.
  - rewrite /=IH/= plus_n_Sm. ring.
Qed.
Lemma eval_app: forall P Q (x: R), eval (P ++ Q) x = eval P x + eval_ (length P) Q x.
Proof. intros; rewrite /eval eval_app_ -plus_n_O //. Qed.

Lemma ClenshawR b c P x : Clenshaw b c P x = eval (rev_append P [c - 2 * x * b;b]) x.
Proof.
  revert b c; induction P as [|a P IH]; intros.
  + compute. rewrite !T0 !T1 /=. ring.
  + rewrite /=IH/= 2!rev_append_rev 2!eval_app /=TSS/=. ring. 
Qed.

(** the two evaluation strategies coincide (on R) *)
Corollary evalR P x: eval' P x = eval P x.
Proof. rewrite /eval' ClenshawR rev_append_rev rev_involutive eval_app /=. ring. Qed.



Lemma prim_consSS_ n (a: R) p : prim_ n.+2 (a :: p) =
  sadd [0 - a // ((n.+1)*2); 0; a // ((n.+3)*2)] (cons0 (prim_ n.+3 p)).
Proof. reflexivity. Qed.

Lemma eval_prim_ n p x : Derive (eval_ n.-1 (prim_ n p)) x = eval_ n p x.
Proof.
  revert n. 
  induction p as [ | a p IHp]; intros n; [| destruct n as [ | [ | ]]]. 
+ by rewrite Derive_const.
+ erewrite Derive_ext.
  rewrite /= -IHp -T_Derive0 -Derive_scal -Derive_plus => //;
    last apply eval_ex_derive_; try auto_derive; try repeat split; apply T_ex_derive.
  intro; rewrite /= eval_add_ /= T0 T1; field.
+ erewrite Derive_ext.
  rewrite /= -IHp -T_Derive1 -Derive_scal -Derive_plus => //;
    last apply eval_ex_derive_; auto_derive; repeat split; last apply T_ex_derive; auto_derive => //.
  intro; rewrite /= eval_cons0_ eval_add_ /= T1; field.
+ erewrite Derive_ext.
  rewrite /= -IHp -T_DeriveSS -Derive_scal -Derive_plus => //; last apply eval_ex_derive_.
  apply ex_derive_scal, ex_derive_minus with (f:=fun t => _*T _ t); apply ex_derive_scal; apply T_ex_derive.
  intro. rewrite prim_consSS_ eval_add_.
  replace (eval_ n.+2.-1 (0 :: prim_ n.+3 p) t) with (eval_ n.+3.-1 (prim_ n.+3 p) t); last by compute; ring.
  rewrite -!RdivN !mult_INR !INRS eval_cons0_ /=.
    by field; split; rewrite -?INRS; apply not_0_INR.
Qed.

Lemma eval_prim_Derive p x : Derive (eval (prim p)) x = eval p x.
Proof. apply (eval_prim_ 0). Qed.

Lemma integrateE p a b : integrate p a b = RInt (eval p) a b.
Proof.
  unfold integrate. rewrite 2!evalR. apply integrate_prim.
  apply T_cont. apply T_ex_derive. apply eval_prim_Derive.
Qed.

Lemma lohi: lo < hi.
Proof. cbv; lra. Qed.

Lemma eval_range_ x (Hx: lo<=x<=hi): forall p n, Rabs (eval_ n p x) <= range_ p.
Proof.
  elim => [ | a q IH] n /=.
  + rewrite Rabs_R0; lra.
  + setoid_rewrite Rabs_triang. apply Rplus_le_compat.
    rewrite Rabs_mult. transitivity (Rabs a * 1). 2: simpl; lra.
    apply Rmult_le_compat_l. apply Rabs_pos. 
    generalize (@T_range n x). rewrite /lo /hi /= in Hx.
    clear IH; split_Rabs; simpl in *; lra.
    apply IH. 
Qed.

Lemma eval_range (p: list R) (x: R) (Hx: lo<=x<=hi): (range p).1 <= eval p x <= (range p).2.
Proof.
  rewrite /range/eval. destruct p as [|a q]=>/=.
  - lra.
  - rewrite T0. generalize (eval_range_ Hx q 1). simpl. split_Rabs; lra. 
Qed.


(** ** parametricity of the operations 
    above, we have only specified the instance of the operations on R
    by proving the following parametricity results, we intuitively obtain that they are valid for all instances which are coherent with R (this will be the case with intervals, I).

    those proofs are mostly automatic.
 *)

Section s.
 Context {R S: Ops1}.
 Variable T: Rel1 R S.
 Notation pT := (list_rel T).

 Lemma rcons0: forall x y, pT x y -> pT (cons0 x) (cons0 y).
 Proof. intros ??[|]=>/=; rel. Qed.
 Lemma rcons00: forall x y, pT x y -> pT (cons00 x) (cons00 y).
 Proof. intros ??[|]=>/=; rel. Qed.
 Hint Resolve rcons0 rcons00: rel.
 Lemma rmul_minus: forall x y, pT x y -> forall x' y', pT x' y' -> pT (mul_minus x x') (mul_minus y y').
 Proof. intros ?? H; induction H; intros ?? [|???]; simpl; rel. Qed.
 Lemma rmul_plus: forall x y, pT x y -> forall x' y', pT x' y' -> pT (mul_plus x x') (mul_plus y y').
 Proof. intros ?? H; induction H; intros ?? [|???]; simpl; rel. Qed.
 Hint Resolve rmul_minus rmul_plus: rel.
 Lemma rpmul: forall x y, pT x y -> forall x' y', pT x' y' -> pT (pmul x x') (pmul y y').
 Proof. simpl. unfold pmul. rel. Qed.
 Lemma rpone: pT pone pone.
 Proof. simpl. unfold pone. rel. Qed.
 Lemma rpid: pT pid pid.
 Proof. simpl. unfold pid. rel. Qed.
 Lemma rpcst: forall a b, rel T a b -> pT (pcst a) (pcst b).
 Proof. unfold pcst. rel. Qed.
 Lemma rClenshaw: forall P Q, pT P Q ->
                  forall a b, T a b ->
                  forall c d, T c d ->
                  forall x y, rel T x y -> rel T (Clenshaw a c P x) (Clenshaw b d Q y).
 Proof. induction 1; simpl; rel. Qed.
 Lemma reval: forall P Q, pT P Q -> forall x y, rel T x y -> rel T (eval' P x) (eval' Q y).
 Proof. intros. apply rClenshaw; rel. Qed.
 Lemma rprim_: forall p q, pT p q -> forall n, pT (prim_ n p) (prim_ n q).
 Proof. induction 1. constructor; simpl. destruct n as [|[|n]]; simpl; rel. Qed.
 Hint Resolve reval rprim_: rel.
 Lemma rprim: forall p q, pT p q -> pT (prim p) (prim q).
 Proof. unfold prim. rel. Qed.
 Hint Resolve rprim: rel.
 Lemma rintegrate: forall p q, pT p q ->
                   forall a b, T a b ->
                   forall c d, T c d ->
                               T (integrate p a c) (integrate q b d).
 Proof. unfold integrate. rel. Qed.
 Lemma rlo: T lo lo.
 Proof. unfold lo; rel. Qed. 
 Lemma rhi: T hi hi.
 Proof. unfold hi; rel. Qed. 
 Lemma rrange_ p q: pT p q -> T (range_ p) (range_ q).
 Proof. induction 1; simpl; rel. Qed.
 Lemma rrange p q: pT p q -> pair_rel T (range p) (range q).
 Proof.
   pose proof rrange_. 
   rewrite /range. intros [|a b AB p' q' p'q']; rel.
 Qed.
End s.




(** ** interpolation  *)
Section i.
 Import interfaces.
 Context {C: Ops1}.
 Variable n: Z.
 Variable f: C -> C.

 Let dn: Z := 2*n.
 Let sn: Z := n+1.
 Let cn: C := fromZ n.

 (** interpolation points *)
 Let point: Z -> C :=
   Zmap.get 0 (
     Zmap.mk (fun i => cos (mulZ i (pi / cn))) dn).

 (** values at interpolation points *)
 Let value: Z -> C :=
   Zmap.get 0 (
     Zmap.mk (fun i => f (point i)) sn).

 Let DCTinv_coeff_aux (i j: Z): C :=
   Zfold' (fun j acc => acc +
     if Z.ltb j n 
     then mulZ 2 (value j * point ((i*j) mod dn))
     else         value j * point ((i*j) mod dn)
         ) j (value 0).
 Let DCTinv_coeff (i: Z): C :=
   (if Z.eqb i 0 then divZ 2 else ssrfun.id)
     (DCTinv_coeff_aux i n / cn).
 
 Definition interpolate: list C :=
   Zmap.tolist 0 sn (Zmap.mk DCTinv_coeff sn).
End i.


(** packing everything together, we get a basis *)

Definition basis11_ops_on (C: Ops1): BasisOps_on C := {|
  vectorspace.lo := fromZ (-1);
  vectorspace.hi := 1;
  vectorspace.bmul := pmul;
  vectorspace.bone := pone;
  vectorspace.bid := ret pid;
  vectorspace.bcos := err "cos not available in Chebyshev basis";
  vectorspace.bsin := err "sin not available in Chebyshev basis";
  vectorspace.bintegrate := integrate;
  vectorspace.beval := @eval' C;
  vectorspace.brange := Some range;
  vectorspace.interpolate := interpolate
|}.

Definition basis11_ops {N: NBH}: BasisOps := {|
  BI := basis11_ops_on II;
  BF := basis11_ops_on FF;
|}.

(* TOTHINK: avoid the rescaling when [[lo;hi]] = [[-1;1]]? *)
Definition basis_ops {N: NBH} (lo hi: II): BasisOps :=
  rescale_ops basis11_ops lo hi.

Program Definition basis11 {N: NBH}: Basis basis11_ops := {|
  TT := T;
  BR := basis11_ops_on _;
  vectorspace.lohi := lohi;
  vectorspace.evalE := evalR;
  vectorspace.basis_cont := T_cont;
  vectorspace.eval_mul := eval_mul;
  vectorspace.eval_one := eval_one;
  vectorspace.eval_id := ep_ret eval_id;
  vectorspace.integrateE := integrateE;
  vectorspace.eval_range := eval_range;
  vectorspace.rlo := rfromZ _ (-1);
  vectorspace.rhi := @rone _ _ _;
  vectorspace.rbmul := @rpmul _ _ (contains (NBH:=N));
  vectorspace.rbone := @rpone _ _ _;
  vectorspace.rbid := er_ret (@rpid _ _ _);
  vectorspace.rbintegrate := @rintegrate _ _ _;
  vectorspace.rbeval := @reval _ _ _;
  vectorspace.rbrange := @rrange _ _ _;
|}.

Definition basis {N: NBH} (D: Domain): Basis (basis_ops dlo dhi) := rescale basis11 D.
