(** * Operations on monomial basis (to obtain Taylor models) *)

Require Import String.
Require Import vectorspace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition M k x := x^k.

(** naive evaluation (defined in vectorspace) *)
Notation eval_ := (eval_ M).
Notation eval := (eval M).


(** continuity/derivability properties *)

Lemma M_cont n x : continuity_pt (M n) x.
Proof.
  induction n as [ | n IHn].
+ now apply continuity_const.
+ unfold M; simpl; apply continuity_pt_mult.
  unfold continuity_pt; unfold continue_in; unfold limit1_in; unfold limit_in.
  now intros eps Heps; exists eps; split; first apply Heps; intros t.
  apply IHn.
Qed.


Lemma M_ex_derive n x : ex_derive (M n) x.
Proof. apply ex_derive_pow; apply ex_derive_id. Qed.

Lemma M_Derive n x : Derive (M n.+1) x = INR n.+1 * M n x.
Proof.
  rewrite /M Derive_pow; last apply ex_derive_id.
  rewrite Derive_id /=; ring.
Qed.

Lemma eval_ex_derive_ n P x: ex_derive (eval_ n P) x.
Proof. apply eval_ex_derive_basis_, M_ex_derive. Qed. 
Lemma eval_ex_derive P x: ex_derive (eval P) x.
Proof. apply eval_ex_derive_. Qed. 


(** ** operations on polynomials *)

(** linear time evaluation (Hörner) *)

Fixpoint eval' {R: Ops0} (P: list R) (x: R): R :=
  match P with
  | [] => 0
  | a::Q => a + x * eval' Q x
  end. 
Lemma evalE P x: eval' P x = eval P x.
Proof.
  assert(H: forall n, eval_ n P x = eval' P x * x ^ n).
  induction P as [|a Q IH]; intro; simpl; unfold M; rewrite ?IH; simpl; ring.
  unfold eval. rewrite H. simpl. lra. (* BUG: ring fails *)
Qed.
Lemma evalN x: eval [] x = 0.
Proof. reflexivity. Qed.
Lemma evalC a Q x: eval (a::Q) x = a + x * eval Q x.
Proof. by rewrite -evalE /= evalE. Qed.

(** same as [eval'], but with truncated multiplications *)
Fixpoint eval'' {C: Ops0} d (P: list C) (x: C): C :=
  match P with
  | [] => 0
  | a::Q => a + x *[d] eval'' d Q x
  end.
(* Lemma eval''E d (P: list R) (x: R): eval'' d P x = eval' P x. *)
(* Proof. elim: P=>//=a q H. congruence. Qed. *)
Definition eval't {C: Ops0} d :=
  match d with
  | Some d => @eval'' C d
  | None => @eval' C
  end.

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

 (** derivation *)
 Fixpoint derive_ (n: Z) (P: poly) :=
   match P with
   | [] => []
   | x::P => mulZ n x :: derive_ (n.+1) P
   end.
 Definition derive P := derive_ 1 (tl P).

 (** primitive *)
 Fixpoint prim_ (n: Z) (P: poly) :=
   match P with
   | [] => []
   | x::P => x//n :: prim_ (n.+1) P
   end.
 Definition prim P := 0::prim_ 1 P.

 (** integration *)
 Definition integrate p a b :=
   let q := prim p in eval' q b - eval' q a. 

End r.


(** interpolation (not implemented for monomial basis, for now) *)
Definition interpolate {C: Ops1} (deg: Z)(f: C -> C): list C := [].


(** ** correctness of the above operations, on R *)

Lemma eval_cst a (x: R): eval (scst a) x = a.
Proof. compute. ring. Qed.

Lemma eval_one (x: R): eval sone x = 1.
Proof. compute. ring. Qed.

Lemma eval_id (x: R): eval sid x = x.
Proof. compute. ring. Qed.

Lemma eval_mul: forall P Q (x: R), eval (smul P Q) x = eval P x * eval Q x.
Proof.
  induction P as [|a P IH]; intros Q x; simpl. cbn; ring.
  rewrite eval_add eval_scal 2!evalC IH /=. ring. 
Qed.

Lemma eval_comp: forall P Q (x: R), eval (comp P Q) x = eval P (eval Q x).
Proof.
  induction P as [|a P IH]; intros Q x; simpl. reflexivity. 
  rewrite eval_add eval_mul eval_cst evalC IH /=. ring. 
Qed.

Lemma deriveS P x: forall k,
  eval (derive_ (k.+1) P) x =  eval P x + eval (derive_ k P) x.
Proof.
  induction P as [|a p IHP]=>k /=. cbv; ring.
  rewrite 3!evalC /= IHP.
  rewrite succ_IZR/=. ring. 
Qed.

Lemma derive0 P x: eval (derive_ 0 P) x =  x * eval (derive P) x.
Proof. destruct P=>/=. cbn; ring. rewrite evalC; cbn; ring. Qed.  

Lemma derive1 P x: eval (derive P) x =  eval (tl P) x + x * eval (derive (tl P)) x.
Proof. by rewrite {1} (deriveS _ _ 0) derive0. Qed.

Lemma eval_derive (P : list R) x: eval (derive P) x = Derive (eval P) x.
Proof.
  elim : P => [ | a p IHP ] /=.
  + by rewrite /f_cst Derive_const.
    rewrite (Derive_ext _ _ _ (evalC a p)). 
    rewrite Derive_plus. rewrite Derive_const Derive_mult.
    rewrite -IHP Derive_id derive1 /=; lra.
    apply ex_derive_id. apply eval_ex_derive. 
    apply ex_derive_const. apply ex_derive_mult. apply ex_derive_id. apply eval_ex_derive. 
Qed.

Lemma is_derive_eval (P : list R) (x:R):
  is_derive (eval P) x (eval (derive P) x).
Proof. rewrite eval_derive. apply Derive_correct, eval_ex_derive. Qed.  

Lemma eval_prim_ n p x : Derive (eval_ n.+1 (prim_ (Z.of_nat n.+1) p)) x = eval_ n p x.
Proof.
  elim: p n => [ | a p IHp] n. 
+ by rewrite /=Derive_const.
+ rewrite Derive_plus; last apply eval_ex_derive_; rewrite -/eval_ -/prim_.
  rewrite Derive_scal -Nat2Z.inj_succ IHp M_Derive.
  rewrite INR_IZR_INZ. cbn; field.
  fold (Z.of_nat (n.+1)). rewrite -INR_IZR_INZ. by apply (not_0_INR n.+1).
  apply ex_derive_scal; apply (M_ex_derive n.+1).
Qed.

Lemma eval_prim_Derive p x : Derive (eval (prim p)) x = eval p x.
Proof.
  rewrite /prim /eval /=.
  rewrite Derive_plus; last apply eval_ex_derive_; last apply ex_derive_const.
  rewrite Derive_const eval_prim_; ring.
Qed.

Lemma integrateE p a b : integrate p a b = RInt (eval p) a b.
Proof.
  unfold integrate. rewrite 2!evalE. apply integrate_prim.
  apply M_cont. apply M_ex_derive. apply eval_prim_Derive.
Qed.

(** ** parametricity of the operations  *)

Section s.
 Context {R S: Ops0}.
 Variable T: Rel0 R S.
 Notation sT := (list_rel T).
 Lemma smulR: forall x y, sT x y -> forall x' y', sT x' y' -> sT (smul x x') (smul y y').
 Proof. induction 1; rel. Qed.
 Lemma soneR: sT sone sone.
 Proof. rel. Qed.
 Lemma sidR: sT sid sid.
 Proof. rel. Qed.
 Lemma scstR: forall a b, rel T a b -> sT (scst a) (scst b).
 Proof. rel. Qed.
 Lemma XkR k: sT (Xk k) (Xk k).
 Proof. induction k; rel. Qed.
 Lemma compR: forall x y, sT x y -> forall x' y', sT x' y' -> sT (comp x x') (comp y y').
 Proof. move: smulR scstR=>? ?; induction 1; rel. Qed.
 Lemma evalR: forall P Q, sT P Q -> forall x y, T x y -> T (eval' P x) (eval' Q y).
 Proof. induction 1; rel. Qed.
 Lemma eval'R: forall d P Q, sT P Q -> forall x y, T x y -> T (eval'' d P x) (eval' Q y).
 Proof. induction 1; rel. Qed.
 Lemma eval'tR: forall d P Q, sT P Q -> forall x y, T x y -> T (eval't d P x) (eval' Q y).
 Proof. destruct d. apply eval'R. apply evalR. Qed.
End s.

Section s'.
 Context {R S: Ops0}.
 Variable T: Rel0 R S.
 Notation sT := (list_rel T).
 Lemma derive_R : forall x y, sT x y -> forall n , sT (derive_ n x) (derive_ n y).
 Proof. induction 1; rel. Qed.
 Lemma deriveR : forall x y, sT x y -> sT (derive x) (derive y).
 Proof. move: derive_R; rel. Qed.
 Lemma prim_R: forall x y, sT x y -> forall n, sT (prim_ n x) (prim_ n y).
 Proof. induction 1; rel. Qed.
 Lemma primR: forall x y, sT x y -> sT (prim x) (prim y).
 Proof. move: prim_R; rel. Qed.
 Lemma integrateR: forall p q, sT p q ->
                   forall a b, T a b ->
                   forall c d, T c d ->
                               T (integrate p a c) (integrate q b d).
 Proof. move: primR (evalR (T:=T)); rel. Qed.
End s'.

(** packing everything together, we get a basis *)

Definition basis_ops_on (C: Ops1) (lo hi: C): BasisOps_on C := {|
  vectorspace.lo := lo;
  vectorspace.hi := hi;
  vectorspace.bmul := smul;
  vectorspace.bone := sone;
  vectorspace.bid := ret sid;
  vectorspace.bcos := err "cos not available in Taylor basis";
  vectorspace.bsin := err "sin not available in Taylor basis";
  vectorspace.bintegrate := integrate;
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
  vectorspace.evalE := evalE;
  vectorspace.basis_cont := M_cont;
  vectorspace.eval_mul := eval_mul;
  vectorspace.eval_one := eval_one;
  vectorspace.eval_id := ep_ret eval_id;
  vectorspace.integrateE := integrateE;
  vectorspace.eval_range := I;
  vectorspace.loR := dloR;
  vectorspace.hiR := dhiR;
  vectorspace.bmulR := @smulR _ _ (contains (NBH:=N));
  vectorspace.boneR := @soneR _ _ _;
  vectorspace.bidR := er_ret (@sidR _ _ _);
  vectorspace.bintegrateR := @integrateR _ _ _;
  vectorspace.bevalR := @evalR _ _ _;
  vectorspace.brangeR := I;
|}.



(** polynomials with functional coefficients *)
Section f.
 Context {A: Type} {C: Ops0}.
 Notation Fun := (A -> C).

 (** evaluation of the coefficients at a given point [t] *)
 Definition apply (P: list Fun) (t: A): list C := map (fun h => h t) P.

 Lemma eval'_apply (P : list Fun) s (t :A): eval' (apply P t) (s t) = eval' P s t.
 Proof. by elim: P => [ // | h P IHP /=];rewrite /f_bin IHP. Qed.


 (** commutation with the various operations *)
 Lemma apply_opp (P : list Fun) t: apply (sopp P) t = sopp (apply P t).
 Proof. 
   elim : P => [ //= | a P IHP /=]. by rewrite /f_bin /f_cst IHP.
 Qed. 
 
 Lemma apply_add (P Q: list Fun) t: apply (sadd P Q) t = sadd (apply P t) (apply Q t).
 Proof.
   move : Q; elim : P => [ Q // | a p IHP [ // | b Q ] /= ]; by rewrite /f_bin IHP.
 Qed.
 
 Lemma apply_sub P Q t: apply (ssub P Q) t = ssub (apply P t) (apply Q t).
 Proof. by rewrite /ssub apply_add apply_opp /=. Qed.
 
 Lemma apply_scal P K t: apply (sscal K P) t = sscal (K t) (apply P t).
 Proof.
   elim : P => [ | a P IHP /= ] //; by rewrite /f_bin IHP. 
 Qed.
 
 Lemma apply_mul (P Q: list Fun) t: apply (smul P Q) t = smul (apply P t) (apply Q t).
 Proof.
   move : Q; elim : P => [ Q // | a p IHP [ // | b Q ] /= ].
   by rewrite IHP. by rewrite /f_bin -apply_scal apply_add IHP.
 Qed.
 
 Lemma apply_id t: apply sid t = sid.
 Proof. by rewrite /sid /= /f_cst. Qed. 
   
 Lemma apply_derive_ n P t: apply (derive_ n P) t = derive_ n (apply P t).
 Proof. move : n;elim : P => [ | h P IHP /=] n //. by rewrite /f_unr IHP. Qed.

 Lemma apply_derive P t: apply (derive P) t = derive (apply P t).
 Proof. move : P => [ | a P /= ] //. apply apply_derive_. Qed.
 
End f.


Lemma eval_apply (P : list (R->R)) s (t: R): eval (apply P t) (s t) = eval' P s t.
Proof. by rewrite -evalE eval'_apply. Qed.

Lemma eval_opp_RinR (P : list (R->R)) s t :
  eval' (sopp P) s t = - (eval' P s t).
Proof. by rewrite -!eval'_apply apply_opp !evalE eval_opp. Qed.

Lemma eval_add_RinR (P Q : list (R->R)) s t :
  eval' (sadd P Q) s t = eval' P s t + eval' Q s t.
Proof. by rewrite -!eval'_apply apply_add !evalE eval_add. Qed.

Lemma eval_sub_RinR (P Q : list (R->R)) s t :
  eval' (ssub P Q) s t = eval' P s t - eval' Q s t.
Proof. by rewrite -!eval'_apply apply_sub !evalE eval_sub. Qed.

Lemma eval_mul_RinR (P Q : list (R->R)) s t :
  eval' (smul P Q) s t = eval' P s t * eval' Q s t.
Proof. by rewrite -!eval'_apply apply_mul !evalE eval_mul. Qed.

Lemma eval_scal_RinR A (P : list (R->R)) s t :
  eval' (sscal A P) s t = A t * eval' P s t.
Proof. by rewrite -!eval'_apply apply_scal !evalE eval_scal. Qed.

Lemma eval_id_RinR (s: R -> R) t: eval' sid s t = s t.
Proof. by rewrite -!eval'_apply apply_id !evalE eval_id. Qed.
