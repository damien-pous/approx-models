(** * Operations on Chebyshev basis *)

Require Import neighborhood vectorspace.

Notation "n .+1" := (S n) (at level 2, left associativity,
  format "n .+1") : nat_scope.
Notation "n .+2" := n.+1.+1 (at level 2, left associativity,
  format "n .+2") : nat_scope.
Notation "n .+3" := n.+2.+1 (at level 2, left associativity,
  format "n .+3") : nat_scope.
Notation "n .+4" := n.+2.+2 (at level 2, left associativity,
  format "n .+4") : nat_scope.

Notation "n .-1" := (Nat.pred n) (at level 2, left associativity,
  format "n .-1") : nat_scope.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Chebyshev polynomials and their basic properties *)
Fixpoint T n x :=
  match n with
  | 0 => 1
  | 1 => x
  | S (S n as m) => 2*x*T m x - T n x
  end.

Lemma TSS n x : T (S (S n)) x = 2*x*T (S n) x - T n x.
Proof. reflexivity. Qed.

Lemma T0 x: T 0 x = 1.
Proof. reflexivity. Qed.

Lemma T1 x: T 1 x = x.
Proof. reflexivity. Qed.

Lemma T2 x: T 2 x = 2 * x^2 - 1.
Proof. simpl. ring. Qed.

Opaque T.

Lemma nat2_ind (P: nat -> Prop) :
  P 0%nat -> P 1%nat -> (forall n, P n -> P (S n) -> P (S (S n))) -> forall n, P n.
Proof.
  intros ???. cut (forall n, P n /\ P (S n)). firstorder.
  induction n; firstorder. 
Qed.  

Lemma Tprod: forall n m (x: R),
    (n<=m)%nat -> T n x * T m x = (T (m+n) x + T (m-n) x) / 2.
Proof.
  intros n m x H. induction n as [| |n IH1 IH2] using nat2_ind. 
  - rewrite T0 Nat.add_0_r Nat.sub_0_r /=; field.
  - rewrite T1. destruct m as [|m]; first by elim: (Nat.nle_succ_0 _ H). 
    rewrite Nat.sub_succ Nat.sub_0_r Nat.add_1_r TSS /=. field. 
  - rewrite TSS /=. ring_simplify.
    rewrite !Rmult_assoc IH1. 2:lia. rewrite IH2. 2: lia. 
    replace (m-n)%nat with (S (S (m-S (S n)))) by lia.
    rewrite TSS. 
    replace (S (m-S (S n))) with (m-S n)%nat by lia.
    rewrite !Nat.add_succ_r !TSS /=. field. 
Qed.

Corollary Tsqr: forall n x, T n x ^ 2 = (T (n+n) x + 1)/2.
Proof. intros. rewrite (pow_add _ 1 1) pow_1 Tprod // Nat.sub_diag //. Qed. 

Lemma T_cont n x : continuity_pt (T n) x.
Proof.
  induction n as [| | n IH1 IH2] using nat2_ind.
  + by apply continuity_pt_const.
  + by apply continuity_pt_id.
  + eapply continuity_pt_ext.
      by move => t; rewrite TSS.
  apply continuity_pt_minus => //.
  apply continuity_pt_mult => //.
  apply continuity_pt_scal, continuity_pt_id.
Qed.

Lemma T_ex_derive n x : ex_derive (T n) x.
Proof.
  induction n as [| | n IH1 IH2] using nat2_ind.
+ eapply ex_derive_ext; first by move => t; rewrite T0.
  apply ex_derive_const.
+ apply ex_derive_id.
+ eapply ex_derive_ext.
  by move => t; rewrite TSS.
  apply ex_derive_minus with (g:=T n) => //.
  apply ex_derive_mult => //.
  apply ex_derive_scal, ex_derive_id.
Qed.

Lemma T_Derive0 x : Derive (T 1) x = T 0 x.
Proof.
  erewrite Derive_ext; last by move => t; rewrite T1.
  by rewrite Derive_id T0.
Qed.

Lemma T_Derive1 x : Derive (fun t => / INR 4 * T 2 t) x = T 1 x.
Proof.
  erewrite Derive_ext; last by move => t; rewrite T2.
  rewrite T1 Derive_scal Derive_minus ?Derive_const ?Derive_scal ?Derive_pow ?Derive_id;
    try repeat auto_derive => //.
  compute; field.
Qed.

Lemma T_DeriveSS n x : Derive (fun t => / (INR ((n.+3)*2)) * T n.+3 t - / (INR ((n.+1)*2)) * T n.+1 t) x = T n.+2 x.
Proof.
  induction n as [| | n IH1 IH2] using nat2_ind.
+ erewrite Derive_ext; first last.
  by move => t; rewrite !TSS !T0 !T1.
  rewrite T2 /=; apply is_derive_unique; auto_derive => //; field.
+ erewrite Derive_ext; first last.
  by move => t; rewrite !TSS !T0 !T1.
  rewrite TSS T2 T1 /=; apply is_derive_unique; auto_derive => //; field.
+ set g := fun t => INR n.+4 / INR n.+1.+4 * ((2*t) * (/ INR ((n.+4)*2) * T n.+4 t - / INR ((n.+2)*2) * T n.+2 t)
    - ( / INR ((n.+3)*2) * T n.+3 t - / INR ((n.+1)*2) * T n.+1 t)
    + / INR n.+2 * (/ INR ((n.+3)*2) * T n.+3 t - / INR ((n.+1)*2) * T n.+1 t)).
have INR0 : INR 0 = 0 by [].
have INR1 : 1%R = INR 1 by [].
have INR2 : 2%R = INR 2 by [].
  rewrite (Derive_ext _ g).
* (*have H' k t : ex_derive [eta (T k)] t
    by apply ex_derive_ext with (f:=T k) => //; apply T_ex_derive.*)
  Opaque INR. 
  rewrite Derive_scal Derive_plus /=; try auto_derive; repeat split; try apply T_ex_derive.
  rewrite Derive_scal IH1 Derive_minus ?IH1; try auto_derive; try repeat split; try apply T_ex_derive.
  rewrite Derive_mult ?Derive_scal ?Derive_id ?IH2; try auto_derive; try repeat split; try apply T_ex_derive.
* rewrite !INR1 !TSS !S_INR !mult_INR !S_INR !INR0 /=; field.
  rewrite -!S_INR INR2 -!mult_INR INR1 -!plus_INR; repeat try split; apply not_0_INR; lia.
* move => t; rewrite /g !TSS !S_INR !mult_INR !S_INR !INR0 /=; field. -
  rewrite -!S_INR INR2 -!mult_INR INR1 -!plus_INR; repeat try split; apply not_0_INR; lia.
  Transparent INR. 
Qed.



Section TnTrigo.

Import Reals.

Lemma T_cos n t : T n (cos t) = cos (INR n * t).
Proof.
  induction n as [| | n IH1 IH2] using nat2_ind.
+ by rewrite /= T0 Rmult_0_l cos_0.
+ by rewrite /= Rmult_1_l T1.
+ rewrite TSS IH1 IH2.
  replace (cos (INR n.+2 * t)) with ((cos (INR n.+2 * t) + cos (INR n * t)) - cos (INR n * t));
    last by rewrite /=; ring.
  rewrite !S_INR /= form1 -!S_INR.
  replace ((INR n.+2 * t - INR n * t) / 2)%R with t. 2: rewrite !S_INR; field.
  replace ((INR n.+2 * t + INR n * t) / 2)%R with (INR n.+1 * t)%R. 2: rewrite !S_INR; simpl; field.
  field. 
Qed.

Lemma cos_range (x : R) : -1 <= x <= 1 -> exists t, 0 <= t <= PI /\ cos t = x.
Proof.
  set PPI := PI.
  replace 0%R with (Rmin 0 PI); last by apply Rmin_left; move: PI_RGT_0; lra.
  replace PPI with (Rmax 0 PI); last by rewrite /PPI; apply Rmax_right; move: PI_RGT_0; lra.
  replace (-1) with (Rmin (cos 0) (cos PI)); last by rewrite cos_0 cos_PI; apply Rmin_right; lra.
  replace 1%R with (Rmax (cos 0) (cos PI)); last by rewrite cos_0 cos_PI; apply Rmax_left; lra.
  move => Hx; move: (IVT_gen _ _ _ _ continuity_cos Hx) => [t Ht].
  by exists t.
Qed.

Lemma T_range n x : -1 <= x <= 1 -> -1 <= T n x <= 1.
Proof.
  move => Hx; move: (cos_range Hx) => [t [_ Ht]].
  rewrite -Ht T_cos.
  apply COS_bound.
Qed.

End TnTrigo.

(** naive evaluation (defined in vectorspace) *)
Notation eval_ := (eval_ T).
Notation eval := (eval T).

Definition eval_cont := eval_cont_basis T_cont.
Definition eval_ex_RInt := eval_ex_RInt T_cont.

Lemma eval_ex_derive_ n P x: ex_derive (eval_ n P) x.
Proof.
  elim: P n => [ | a P IHP] n /=.
  + apply ex_derive_const.
  + auto_derive; repeat try split => //; apply T_ex_derive.
Qed.

Lemma eval_ex_derive P x : ex_derive (eval P) x.
Proof. apply eval_ex_derive_. Qed.


(* forgot to mention in the paper that this lemma is important for [eval_mul] *)
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

(** ** definition of the operations *)

Section r.
 Context {C: Ops1}.

 (** linear time evaluation (Clenshaw) *)
 Fixpoint Clenshaw b c (P: seq C) x :=
   match P with
   | [::] => c - x*b
   | a::Q => Clenshaw c (a + fromZ 2*(x*c) - b) Q x 
   end.
 Definition eval' P x := Clenshaw 0 0 (rev P) x.

 (* constant *)
 Definition scst a: seq C := [::a].

 (* one *)
 Definition sone: seq C := [::1].

 (** identity (X) *)
 Definition sid: seq C := [::0;1].
 
 (** multiplication *)
 Fixpoint mul_minus (p q: seq C): seq C :=
   match p,q with
   | [::],_ | _,[::] => [::]
   | a :: p', b :: q' => sadd (a*b :: (sadd (sscal a q') (sscal b p'))) (mul_minus p' q')
   end.
 
 Fixpoint mul_plus (p q: seq C): seq C :=
   match p,q with
   | [::],_ | _,[::] => [::]
   | a :: p', b :: q' => sadd (a*b :: (sadd (sscal a q') (sscal b p'))) (cons00 (mul_plus p' q'))
   end.
 
 Definition smul (p q: seq C): seq C := sscal (1//2) (sadd (mul_minus p q) (mul_plus p q)).

 (** primitive  *)
 Fixpoint prim_ (n : nat) (p : seq C) : seq C :=
  match p with
    | [::] => [::]
    | a :: q =>
      match n with
        | 0 => sadd [:: 0; a] (prim_ 1 q)
        | 1 => 0 :: (sadd [:: 0; a // 4] (prim_ 2 q))
        | n'.+2 => sadd [:: 0 - a // ((n'.+1)*2)%nat; 0; a // ((n.+1)*2)%nat]
                        (cons0 (prim_ n.+1 q))
      end
  end.
 Definition prim p := prim_ 0 p.

 (** domain *)
 Definition lo: C := 0-1.
 Definition hi: C := 1.

 (** range *)
 Definition range_: seq C -> C := foldr (fun a x => abs a + x) 0.
 Definition range' p: C*C :=
   match p with
   | [::] => (0,0)
   | a :: q => let r := range_ q in (a-r,a+r)
   end.

End r.


(** ** interpolation  *)

(** basic utilities: partial fixpoint operator, maps on [Z],   *)
Section powerfix.
Variables A B: Type.
Notation Fun := (A -> B).
Fixpoint powerfix' n (f: Fun -> Fun) (k: Fun): Fun := 
  fun a => match n with O => k a | S n => f (powerfix' n f (powerfix' n f k)) a end.
Definition powerfix n f k a := f (powerfix' n f k) a.
Definition Fix := powerfix 100.
End powerfix.
Definition Zfold A (f: Z -> A -> A): Z -> A -> A :=
  Fix (fun Zfold z a => if Z.eqb z 0 then a else let z:=Z.pred z in Zfold z (f z a)) f.
Definition Zfold' A (f: Z -> A -> A): Z -> A -> A :=
  Fix (fun Zfold z a => if Z.eqb z 0 then a else let z':=Z.pred z in Zfold z' (f z a)) f.
Require Import FSets.FMapPositive.
Module Zmap.
  Definition t := PositiveMap.t.
  Definition empty {A} := @PositiveMap.empty A.
  Definition add {A} i (v: A) m :=
    match i with
    | Z0 => PositiveMap.add xH v m
    | Zpos p => PositiveMap.add (Pos.succ p) v m
    | _ => m
    end.
  Definition find {A} m i: option A :=
    match i with
    | Z0 => PositiveMap.find xH m
    | Zpos p => PositiveMap.find (Pos.succ p) m
    | _ => None
    end.
  Definition map_below {A} n (f: A -> A) :=
    let n := match n with Zpos p => Pos.succ p | _ => xH end in
    PositiveMap.mapi (fun i x => if Pos.leb i n then f x else x).
  Definition get {A} d m i: A := match find m i with Some v => v | None => d end. 
  Definition mk {A} (f: Z -> A) n := Zfold (fun z => add z (f z)) n empty.
  Definition toseq {A} d n m: seq A := Zfold (fun z s => get d m z :: s) n [::].
End Zmap.


(** interpolation *)
Section i.
 Context {C: Ops1}.
 Variable n: Z.
 Variable f: C -> C.

 Let dn: Z := (2*n)%Z.
 Let n': C := fromZ n.
 Let two:C := fromZ 2.

 Let DCTinv_coeff_aux vl (pt: Z -> C) (i j: Z): C :=
   Zfold' (fun j acc => acc +
     if Z.ltb j n then 
       two * vl j * pt ((i*j) mod dn)%Z
     else
       vl j * pt ((i*j) mod dn)%Z
         ) j (vl 0%Z).

 Let points: Zmap.t C :=
   Zmap.mk (fun i => cos (fromZ i * pi / n')) dn.

 Let values :=
   Zmap.mk (fun i => f (Zmap.get 0 points i)) (n+1)
           (* Zmap.map_below n f points *)
 .

 Let DCTinv_coeff (i: Z) :=
   (if Z.eqb i 0%Z then dvn 2 else ssrfun.id)
     (DCTinv_coeff_aux (Zmap.get 0 values) (Zmap.get 0 points) i n / n').

 Definition interpolate := Zmap.toseq 0 (n+1) (Zmap.mk DCTinv_coeff (n+1)).
End i.

Definition basis: BasisOps T :=
  fun C => {|
    vectorspace.lo := lo;
    vectorspace.hi := hi;
    vectorspace.bmul := smul;
    vectorspace.bone := sone;
    vectorspace.bid := sid;
    vectorspace.bprim := prim;
    vectorspace.beval := @eval' C;
    vectorspace.brange := Some range';
    vectorspace.interpolate := interpolate
  |}.


(** ** correctness of the operations on reals *)

Lemma ClenshawR b c P x : Clenshaw b c P x = eval (catrev P [::c - 2 * x * b;b]) x.
Proof.
  revert b c; induction P as [|a P IH]; intros.
  + compute. rewrite !T0 !T1 /=. ring.
  + rewrite /=IH/= 2!catrevE 2!eval_app /=TSS/=. ring. 
Qed.

Lemma evalR P x: eval' P x = eval P x.
Proof. rewrite /eval' ClenshawR catrevE rev_rev eval_app /=. ring. Qed.

Lemma eval_cst a (x: R): eval (scst a) x = a.
Proof. compute. rewrite T0/=. ring. Qed.

Lemma eval_one (x: R): eval sone x = 1.
Proof. compute. rewrite T0/=. ring. Qed.

Lemma eval_id (x: R): eval sid x = x.
Proof. compute. rewrite T0 T1/=. ring. Qed.
       
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

Lemma eval_mul: forall P Q (x: R), eval (smul P Q) x = eval P x * eval Q x.
Proof.
intros. rewrite /eval eval_mul_ /smul eval_scal_ eval_add_/= /Rdiv /=. ring. Qed.


Lemma prim_consSS_ n (a: R) p : prim_ n.+2 (a :: p) =
  sadd [:: 0 - a // ((n.+1)*2)%nat; 0; a // ((n.+3)*2)%nat] (cons0 (prim_ n.+3 p)).
Proof. by []. Qed.

Lemma eval_prim_ n p x : Derive (eval_ n.-1 (prim_ n p)) x = eval_ n p x.
Proof.
  elim: p n => [ n | a p IHp [ /= | [ /= | n]]]. 
+ by rewrite Derive_const.
+ erewrite Derive_ext.
  rewrite -IHp -T_Derive0 -Derive_scal -Derive_plus => //;
    last apply eval_ex_derive_; try auto_derive; try repeat split; apply T_ex_derive.
  move => t /=; rewrite eval_add_ /= T0 T1; field.
+ erewrite Derive_ext.
  rewrite -IHp -T_Derive1 -Derive_scal -Derive_plus => //;
    last apply eval_ex_derive_; auto_derive; repeat split; last apply T_ex_derive; auto_derive => //.
  move => t /=; rewrite eval_add_ T0 /= T1; field.
+ erewrite Derive_ext.
  rewrite /= -IHp -T_DeriveSS -Derive_scal -Derive_plus => //; last apply eval_ex_derive_.
  apply ex_derive_scal, ex_derive_minus with (f:=fun t => _*T _ t); apply ex_derive_scal; apply T_ex_derive.
  move => t. rewrite prim_consSS_ eval_add_.
  replace (eval_ n.+2.-1 (0 :: prim_ n.+3 p) t) with (eval_ n.+3.-1 (prim_ n.+3 p) t); last by compute; ring.
rewrite /dvn -!RfromN !mult_INR !S_INR eval_cons0_ /=.
by field; split; rewrite -?S_INR; apply not_0_INR.
Qed.

Lemma eval_prim_Derive p x : Derive (eval (prim p)) x = eval p x.
Proof. apply (eval_prim_ 0). Qed.

Lemma eval_prim p a b : eval (prim p) b - eval (prim p) a = RInt (eval p) a b.
Proof.
  rewrite -(RInt_ext (Derive (eval (prim p)))); last by move => t _; rewrite
                                                                       eval_prim_Derive.
  rewrite RInt_Derive. by [].
* move => t _; apply eval_ex_derive.
* move => t _; apply continuous_ext with (f:= eval p); first by move => u; rewrite eval_prim_Derive.
  apply continuity_pt_filterlim; apply eval_cont.
Qed.

Lemma eval_prim' p a b : is_RInt (eval p) a b (eval (prim p) b - eval (prim p) a).
Proof. rewrite eval_prim; apply (RInt_correct (eval p)). apply eval_ex_RInt. Qed.

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

Lemma eval_range' (p: seq R) (x: R) (Hx: lo<=x<=hi): (range' p).1 <= eval p x <= (range' p).2.
Proof.
  rewrite /range'/eval. destruct p as [|a q]=>/=.
  - lra.
  - rewrite T0. generalize (eval_range_ Hx q 1). simpl. split_Rabs; lra. 
Qed.

(** ** parametricity of the operations  *)

Section s.
 Context {R S: Ops1}.
 Variable T: Rel1 R S.
 Notation sT := (seq_rel T).
 Lemma rmul_minus: forall x y, sT x y -> forall x' y', sT x' y' -> sT (mul_minus x x') (mul_minus y y').
 Proof. intros ?? H; induction H; intros ?? [|???]; simpl; rel. Qed.
 Lemma rmul_plus: forall x y, sT x y -> forall x' y', sT x' y' -> sT (mul_plus x x') (mul_plus y y').
 Proof. intros ?? H; induction H; intros ?? [|???]; simpl; rel. Qed.
 Local Hint Resolve rmul_minus rmul_plus: rel.
 Lemma rsmul: forall x y, sT x y -> forall x' y', sT x' y' -> sT (smul x x') (smul y y').
 Proof. simpl. unfold smul. rel. Qed.
 Lemma rsone: sT sone sone.
 Proof. simpl. unfold sone. rel. Qed.
 Lemma rsid: sT sid sid.
 Proof. simpl. unfold sid. rel. Qed.
 Lemma rscst: forall a b, rel T a b -> sT (scst a) (scst b).
 Proof. unfold scst. rel. Qed.
 Lemma rClenshaw: forall P Q, sT P Q ->
                  forall a b, T a b ->
                  forall c d, T c d ->
                  forall x y, rel T x y -> rel T (Clenshaw a c P x) (Clenshaw b d Q y).
 Proof. induction 1; simpl; rel. Qed.
 Lemma reval: forall P Q, sT P Q -> forall x y, rel T x y -> rel T (eval' P x) (eval' Q y).
 Proof. intros. apply rClenshaw; rel. Qed.
 Lemma rprim_: forall p q, sT p q -> forall n, sT (prim_ n p) (prim_ n q).
 Proof. induction 1. constructor; simpl. destruct n as [|[|n]]; simpl; rel. Qed.
 Hint Resolve reval rprim_: rel.
 Lemma rprim: forall p q, sT p q -> sT (prim p) (prim q).
 Proof. unfold prim. rel. Qed.
 Lemma rlo: T lo lo.
 Proof. unfold lo; rel. Qed. 
 Lemma rhi: T hi hi.
 Proof. unfold hi; rel. Qed. 
 Lemma rrange_ p q: sT p q -> T (range_ p) (range_ q).
 Proof. induction 1; simpl; rel. Qed.
 Lemma rrange' p q: sT p q -> pair_rel T (range' p) (range' q).
 Proof.
   pose proof rrange_. 
   rewrite /range'. intros [|a b AB p' q' p'q'] =>//; rel.
 Qed.
End s.

(** packing everything together *)

Instance valid {N: NBH}: ValidBasisOps N basis.
Proof.
  constructor.
  - rewrite /=/lo/hi/=. lra.
  - exact evalR.
  - exact eval_cont.
  - exact eval_mul. 
  - exact eval_one. 
  - exact eval_id. 
  - exact eval_prim'. 
  - exact eval_prim.
  - exact eval_range'.
  - apply rlo. 
  - apply rhi. 
  - apply rsmul.
  - apply rsone.
  - apply rsid.
  - apply rprim. 
  - apply reval. 
  - simpl. apply rrange'.
Qed.
