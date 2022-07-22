(** * Fourier arithmetic of Fourier basis *)

Require Import String Reals.
Require Import vectorspace rescale utils.
Require Import Nat.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



(* rank 2 induction on lists and natural numbers (TODO: move to utils) *)
Fixpoint list_ind2 {C: Type} (P: list C -> Prop)
         (P0: P nil) (P1: forall x, P [x]) (P2: forall x y l, P l -> P (x::y::l)) l: P l.
Proof.
  destruct l. apply P0.
  destruct l. apply P1.
  now apply P2, list_ind2. 
Qed.

Fixpoint nat_ind2 (P: nat -> Prop)
         (P0: P O) (P1: P 1%nat) (P2: forall n, P n -> P (n.+2)) n: P n.
Proof.
  destruct n. apply P0.
  destruct n. apply P1.
  now apply P2, nat_ind2. 
Qed.

(* elements at even/odd positions in a list *)
Section l.
Context {C: Type}.
Fixpoint evens l: list C :=
  match l with
  | [] => []
  | x::l => x::odds l
  end
with odds l: list C :=
  match l with
  | [] => []
  | x::l => evens l
  end.
End l. 

(* basic properties of div2 and even *)
Lemma even_double k: even (2*k).
Proof. induction k=>//. by replace (2*k.+1)%nat with ((2*k).+2) by lia. Qed.
Lemma div2_2n k: div2 (2*k) = k.
Proof. induction k=>//=. rewrite -plus_n_Sm IHk//. Qed.
Lemma div2_2np1 k: div2 ((2*k).+1) = k.
Proof. induction k=>//=. rewrite -plus_n_Sm IHk//. Qed.

(* stupid helper lemma *)
Lemma Pred_eq {A} (P: A -> Prop) a b: a = b -> P a -> P b.
Proof. by intros<-. Qed. 


(** ** Definition of the Fourier Basis and properties *)

Definition order n := if even n then div2 n else  (div2 n).+1.

Lemma orderSS n: order (n.+2) = (order n).+1.
Proof. rewrite /order/=. by case even. Qed.

Lemma orderS n: order (n.+1) = if even n then (order n).+1 else order n.
Proof.
  induction n using nat_ind2=>//.
  rewrite !orderSS IHn /=. by case even.
Qed.

Definition CC n x := cos (INR n * x).
Definition SS n x := sin (INR n * x).
Definition F  n := (if even n then CC else SS) (order n).

Lemma C0 x: CC 0 x = 1.
Proof. by rewrite /CC /= Rmult_0_l cos_0. Qed.         

Lemma S0 x: SS 0 x = 0.
Proof. by rewrite /SS /= Rmult_0_l sin_0. Qed.

Lemma C1 x: CC 1 x = cos x.
Proof. by rewrite /CC /= Rmult_1_l. Qed.

Lemma S1 x: SS 1 x = sin x.
Proof. by rewrite /SS /= Rmult_1_l. Qed. 

Lemma F0 x: F 0 x = 1.
Proof. apply C0. Qed.        

Lemma F1 x: F 1 x = sin x.
Proof. apply S1. Qed.

Lemma F2 x: F 2 x = cos x.
Proof. apply C1. Qed.
  
Lemma form_prod_cos a b: cos a * cos b = (cos (a+b) + cos (a-b))/2.
Proof.
  rewrite /= form1.
  replace ((a + b - (a - b))/2)%R with b%R by lra.
  replace ((a + b + (a - b))/2)%R with a%R by lra.
  field.
Qed.  

Lemma form_prod_sin a b: sin a * sin b = (cos (a-b) - cos(a+b))/2.
Proof.
  rewrite /= form2.
  replace ((a - b - (a + b))/2)%R with (-b)%R by lra.
  replace ((a - b + (a + b))/2)%R with a%R by lra.
  rewrite sin_antisym /=. field.
Qed.

Lemma form_prod_sin_cos a b: sin a * cos b = (sin (a+b) + sin (a-b))/2.
Proof.
  rewrite /= form3.
  replace ((a + b - (a - b)) / 2)%R with b%R by lra.
  replace ((a + b + (a - b)) / 2)%R with a%R by lra.
  field. 
Qed.

Lemma CCprod n m x: (n<=m)%nat -> CC n x * CC m x = (CC (m+n) x + CC (m-n) x)/2.
Proof.
  intro.
  rewrite /CC plus_INR minus_INR => //=.
  rewrite Rmult_plus_distr_r Rmult_minus_distr_r form_prod_cos/=.
  rewrite (cos_sym (INR n * x - INR m * x)).
  rewrite Ropp_minus_distr. do 3 f_equal. ring.
Qed.

Corollary CCsqr n x: CC n x ^ 2 = (CC (n+n) x + 1)/2.
Proof. rewrite (pow_add _ 1 1) pow_1 CCprod // Nat.sub_diag // C0 //. Qed. 

Lemma SSprod n m x: (n<=m)%nat -> SS n x * SS m x = (CC (m-n) x - CC (m+n) x)/2.
Proof.
  intro.
  rewrite /SS /CC plus_INR minus_INR => //=.
  rewrite Rmult_plus_distr_r Rmult_minus_distr_r form_prod_sin/=.
  rewrite (cos_sym (INR n * x - INR m * x)) Ropp_minus_distr Rplus_comm /=. ring. 
Qed.

Corollary SSsqr n x: SS n x ^ 2 = (1 - CC (n+n) x)/2.
Proof. rewrite (pow_add _ 1 1) pow_1 SSprod // Nat.sub_diag // C0 //. Qed.

Lemma SCprod n m x: (n<=m)%nat -> SS n x * CC m x = (SS (m+n) x - SS (m-n) x)/2.
Proof.
  intro.
  rewrite /SS /CC plus_INR minus_INR => //.
  simpl. rewrite Rmult_plus_distr_r Rmult_minus_distr_r form_prod_sin_cos. 
  replace (INR m * x - INR n * x)%R with (- (INR n * x - INR m * x)%R) by ring.
  by rewrite /= sin_antisym /Rminus Ropp_involutive (Rplus_comm (INR n * x)%R (INR m * x)%R). 
Qed.

Corollary SCsqr n x: SS n x * CC n x = (SS (n+n) x)/2.
Proof. rewrite SCprod // Nat.sub_diag // S0 /=. lra. Qed.

Lemma CSprod n m x: (n<=m)%nat -> CC n x * SS m x = (SS (m+n) x + SS (m-n) x)/2.
Proof.
  intro. rewrite /SS /CC plus_INR minus_INR => //.
  by rewrite /= (Rmult_comm (cos (INR n * x)) (sin (INR m * x)))
             Rmult_plus_distr_r Rmult_minus_distr_r form_prod_sin_cos.
Qed.

(** Range of Fourier vectors *)

Lemma F_range n x: -1 <= F n x <= 1.
Proof.
  rewrite /F; case: even.
  - apply COS_bound.
  - apply SIN_bound.
Qed.
  
  
(** Fourier vectors are continuous at every point *)

Lemma CC_cont n x: continuity_pt (CC n) x.
Proof.
  rewrite /CC. apply (continuity_pt_comp (fun t => INR n *t) (fun t => cos t)).
  apply continuity_pt_mult. apply continuity_pt_const. by rewrite /constant. 
  apply continuity_pt_id. apply continuity_cos.
Qed.

Lemma SS_cont n x: continuity_pt (SS n) x.
Proof.
  rewrite /SS. apply (continuity_pt_comp (fun t => INR n *t) (fun t => sin t)).
  apply continuity_pt_mult. apply continuity_pt_const. by rewrite /constant. 
  apply continuity_pt_id. apply continuity_sin.
Qed.

Lemma F_cont n x: continuity_pt (F n) x.
Proof.
  rewrite /F; case: even.
  - apply CC_cont.
  - apply SS_cont.
Qed.

(** Fourier vectors are derivable at every point *)

Lemma CC_ex_derive n x: ex_derive (CC n) x.
Proof.
  rewrite /CC.
  apply (ex_derive_comp  (fun t:R => cos t) (fun t => INR n * t )).
    exists (- (sin( INR  n * x))).  
    apply is_derive_cos.
    apply ex_derive_mult. apply ex_derive_const. apply ex_derive_id.
Qed.

Lemma SS_ex_derive n x: ex_derive (SS n) x.
Proof.
  rewrite /SS.
  apply (ex_derive_comp  (fun t:R => sin t) (fun t => INR n * t )).
    exists (cos( INR  n * x)).  
    apply is_derive_sin.
    apply ex_derive_mult. apply ex_derive_const. apply ex_derive_id.
Qed.

Lemma F_ex_derive n x: ex_derive (F n) x.
Proof.
  rewrite /F; elim: even.
  apply CC_ex_derive. apply SS_ex_derive.
Qed.

(** relations between Fourier vectors and their derivatives *)

Lemma is_derive_scal' (k x: R): is_derive (fun t => scal t k) x k.
Proof. rewrite <- Rmult_1_l. apply @is_derive_scal_l. apply @is_derive_id. Qed.

Lemma Rmult_comm_assoc: forall x y z: R, x*y*z = y*(x*z).
Proof. intros=>/=. ring. Qed.  

Lemma Rmult_opp: forall x: R, -1 * x =  -x. 
Proof. intros=>/=. ring. Qed.

(* TODO: simplify *)
Lemma CC_is_derive n x: is_derive (CC n) x (- INR n * SS n x).
Proof.
  rewrite /CC /SS -Rmult_opp Rmult_comm_assoc Rmult_opp.
  apply (is_derive_comp (fun t:R => cos t) (fun t => INR n * t )). 
  apply is_derive_cos. apply (is_derive_ext (fun t:R => scal t%R (INR  n))). 
  intros. apply Rmult_comm. apply is_derive_scal'. 
Qed.

Lemma SS_is_derive n x: is_derive (SS n) x (INR n * CC n x).
Proof.
  rewrite /SS /CC.
  apply (is_derive_comp (fun t:R => sin t) (fun t => INR n * t )).
  apply is_derive_sin. 
  apply (is_derive_ext (fun t:R => scal t%R (INR n))). 
  intros. apply Rmult_comm. apply is_derive_scal'. 
Qed.

Definition pow_minus_one n := if even n then 1 else -1.

Definition dephase n := if even n then n.-1 else n.+1.

Lemma F_is_derive n x: is_derive (F n) x (pow_minus_one (n+1) * INR (order n) * (F (dephase n) x)).
Proof.
  destruct n. apply is_derive_ext with (fun t => 1). intros; by rewrite F0.
  rewrite /= F0 Rmult_0_r Rmult_0_l /=. apply @is_derive_const.
  rewrite /F /pow_minus_one /dephase Nat.add_comm.
  rewrite Nat.even_succ -Nat.negb_even.
  case_eq (Nat.even n) => He/=; rewrite He/= orderS He ?orderSS.
  rewrite Rmult_1_l. apply SS_is_derive.
  rewrite Rmult_opp. apply CC_is_derive. 
Qed.

Corollary F_is_derive_2n n x: (n>=1)%nat -> is_derive (F (2*n)) x (- INR n * F (2*n - 1) x)%R.
Proof.
  intro Hn.
  move: (F_is_derive (2*n) x). rewrite /pow_minus_one /order /dephase.
  rewrite Nat.add_1_r Nat.even_succ -Nat.negb_even.
  rewrite even_double div2_double/=.
  apply Pred_eq. rewrite Rmult_opp. repeat f_equal. lia.
Qed.

Corollary F_is_derive_2nm1 n x: (n>=1)%nat -> is_derive (F (2*n-1)) x (INR n * F (2*n) x)%R.
Proof.
  intro Hn.
  move: (F_is_derive (2*n-1) x). apply Pred_eq.
  rewrite /pow_minus_one /order /dephase Nat.add_1_r. 
  have He: (even (2*n-1) = false).
   rewrite -Nat.odd_succ -Nat.negb_even.
   replace ((2*n - 1) .+1)%nat with (2*n)%nat by lia.
  by rewrite even_double. 
  rewrite Nat.even_succ -Nat.negb_even He /negb.
  setoid_rewrite Rmult_1_l. cbn -[INR Nat.mul]. repeat f_equal. 2: lia.
  destruct n=>//. rewrite -{2}(div2_2np1 (n.+1))/=. do 2 f_equal. lia. 
Qed.

(** naive evaluation (defined in vectorspace) 
    eval [a b c] x = a * F 0 x + b * F 1 x + c * F 2 x + 0
 *)
Notation evalCC_ := (eval_ CC).
Notation evalCC := (eval CC).
Notation evalSS_ := (eval_ SS). 
Notation evalSS := (eval_ SS 1).
Notation eval_ := (eval_ F).
Notation eval := (eval F).

(** derivability of evaluation *)

Lemma eval_ex_derive_ n P x: ex_derive (eval_ n P) x.
Proof. apply eval_ex_derive_basis_, F_ex_derive. Qed.

Lemma eval_ex_derive P x: ex_derive (eval P) x.
Proof. apply eval_ex_derive_. Qed.


(** ** Operations on trigonometric polynomials
    This time parametrised by a abstract set C of operations.
    Later, C will be instanciated with reals, floating points, and intervals.
 *)

Section ops0.

  Context {C: Ops0}.

  (** constant *)
  Definition pcst a: list C := [a].

  (** one *)
  Definition pone: list C := [1].

  (** cos *)
  Definition pcos: list C := [0;0;1].

  (** sin *)
  Definition psin: list C := [0;1].

  (** helpers for multiplication and fast evaluation *)   
  Fixpoint inject p: list C :=
    match p with
    | [] => []
    | h::q => 0::h::inject q
    end.

  Fixpoint merge h k: list C :=
    match h,k with
    | [],_ => inject k
    | x::h,[] => x::inject h
    | x::h,y::k => x::y::merge h k
    end.
  (* Eval cbn in fun a0 a1 a2 b0 b1 b2 => merge [a0;a1;a2] [b0;b1;b2]. *)
  (* Eval cbn in fun a0 a1 a2 b0 => merge [a0;a1;a2] [b0]. *)
  (* Eval cbn in fun a0 b0 b1 b2 => merge [a0] [b0;b1;b2]. *)

  Fixpoint xrev2 k h: list C :=
    match h with
    | [] => k
    | [x] => 0::x::k
    | x::y::q => xrev2 (y::x::k) q
    end.
  Definition rev2 := xrev2 [].

  Lemma xrev2_app h: forall l k, xrev2 (l++k) h = xrev2 l h++k.
  Proof.
    induction h as [|x|x y q IH] using list_ind2=>l k//=.
    by rewrite -IH.
  Qed.    
  
  Lemma rev2CC x y q: rev2 (x::y::q) = rev2 q++[y;x].
  Proof. by rewrite /rev2 -xrev2_app. Qed.

  Lemma rev2rev l: rev2 l = if even (length l) then rev l else 0::rev l.
  Proof. 
    induction l as [|x|x y q IH] using list_ind2=>//=.
    rewrite rev2CC IH 2!revE. case even=>/=; by rewrite -app_assoc.
  Qed.

  Lemma even_length_xrev2 l: forall k, even (length (xrev2 k l)) = even (length k).
  Proof. induction l as [|x|x y q IH] using list_ind2=>//=k. by rewrite IH. Qed.
  
  Lemma even_length_rev2 l: even (length (rev2 l)).
  Proof. by rewrite even_length_xrev2. Qed.

  Lemma rev2invol l: rev2 (rev2 l) = if even (length l) then l else l++[0].
  Proof.
    rewrite rev2rev even_length_rev2 rev2rev !revE.
    case even=>/=; rewrite rev_involutive//. 
  Qed.
  
  Lemma order_length_rev2 l: even (length l) -> order (length (rev2 l)) = div2 (length l).
  Proof.
    induction l as [|x|x y q IH] using list_ind2=>//=k.
    by rewrite rev2CC app_length/=Nat.add_comm orderSS IH. 
  Qed.
  
  (** multiplication *)  
  Fixpoint mul_minus p q: list C :=
    match p,q with
    | [],_ | _,[] => []
    | a :: p', b :: q' => sadd (a*b :: (sadd (sscal a q') (sscal b p'))) (mul_minus p' q')
    end.

  Fixpoint mul_minusSC p q: list C :=
    match p,q with
    | [],_ | _,[] => []
    | a :: p', b :: q' => sadd (a*b :: (ssub (sscal a q') (sscal b p'))) (mul_minusSC p' q')
    end.
  
  Fixpoint mul_plus p q: list C :=
    match p,q with
    | [],_ | _,[] => []
    | a :: p', b :: q' => sadd (a*b :: (sadd (sscal a q') (sscal b p'))) (cons00 (mul_plus p' q'))
    end.

  Definition pmulCC pC qC :=
    sdivZ 2 (sadd (mul_minus pC qC) (mul_plus pC qC)).

  Definition pmulSS pS qS :=
    sdivZ 2 (ssub (mul_minus pS qS) (cons00 (mul_plus pS qS))).

  Definition pmulSC' pS0 qC :=
    (* Here only, the polynom in sinus pS0 has its first index begining in 0 *)  
    sdivZ 2 (ssub (mul_plus pS0 qC) (mul_minusSC pS0 qC)).

  Definition pmulSC pS qC :=
    tl (pmulSC' (cons0 pS) qC).

  Definition pmul p q :=
    let pC := evens p in
    let pS := odds p in
    let qC := evens q in
    let qS := odds q in
    merge (sadd (pmulCC pC qC) (pmulSS pS qS)) (sadd (pmulSC pS qC) (pmulSC qS pC)).

  (** fast evaluation *)
  Definition fast_eval_ cost sint :=
    fix fast_eval_ a b (P: list C) :=
    match P with
    | [] => a 
    | [_] => 0
    | a'::b'::Q =>
        let a'' := a+a' in
        let b'' := b+b' in
        fast_eval_ ( a''* cost + b'' * sint) (b'' * cost - a'' * sint ) Q
    end.

End ops0.
Section ops1.
  Context {C: Ops1}.

  Definition fast_eval (P: list C) :=
    match P with
    | [] => fun t => 0
    | h::Q => let rQ := rev2 Q in fun t => h + fast_eval_ (cos t) (sin t) 0 0 rQ
    end.

  (** integration *)

  (** primitive of a Fourier polynom without constant coefficient *)
  Fixpoint prim_ (order: Z) (p: list C) :=
    match p with
    | [] => []
    | [b] => [0; 0-b//order]
    | b::a::q => a//order :: 0-b//order :: prim_ (order.+1) q
    end.

  Definition integrate (p: list C) a b :=
    match p with
    | [] => 0
    | h::q => h*(b-a) + let Q := prim_ 1 q in fast_eval (cons0 Q) b - fast_eval (cons0 Q) a
    end.
  
  (** range on C
    since the [F n] have their range in [-1;1], we chose to take the sum of the absolute values of the coefficients. for the constant coefficient, we don't even have to take the absolute value.
    
    TO THINK ... | a cos(nt) + b sin(nt) | <= sqrt ( a^2 + b^2 ) could give a better range, but it would be more expansive to compute...
   *)
  Definition range_: list C -> C := List.fold_right (fun a x => abs a + x) 0.
  Definition range p :=
    match p with
    | [] => (0,0)
    | a::q => let r := range_ q in (a-r,a+r)
    end.
  
End ops1.



(** ** Correctness of the above polynomial operations, on R *)

Lemma eval_cst a x: eval (pcst a) x = a.
Proof. rewrite /pcst /eval /= F0 /=. ring. Qed.

Lemma eval_one x: eval pone x = 1.
Proof. rewrite /pcst /eval /= F0 /=. ring. Qed.

Lemma eval_cos x: eval pcos x = cos x.
Proof. rewrite /pcos /eval /= F2 /=. ring. Qed.

Lemma eval_sin x: eval psin x = sin x.
Proof. rewrite /psin /eval /= F1 /=. ring. Qed.
  
(* multiplication of cosinus polynoms *)
Lemma evalCC_cons00_ n p x: evalCC_ n (cons00 p) x = evalCC_ n.+2 p x.
Proof. destruct p=>//=. ring. Qed.

Lemma CCeval: forall p n m x,
  (n<=m)%nat -> CC n x * evalCC_ m p x = (evalCC_ (m+n) p x + evalCC_ (m-n) p x)/2.
Proof.
  induction p as [|a p IH]; intros n m x H; simpl.
  - field.
  - ring_simplify. rewrite IH. 2: lia. 
    replace (_*CC m x) with (a*(CC n x * CC m x)) by (simpl; ring). 
    rewrite  CCprod //. 
    replace (S m - n)%nat with (S (m-n)) by lia.
    rewrite Nat.add_succ_l /=. field. 
Qed.

Lemma eval_mulCC_: forall pC qCC n x,
    evalCC_ n pC x * evalCC_ n qCC x =
    (evalCC_ 0 (mul_minus pC qCC) x + evalCC_ (n+n) (mul_plus pC qCC) x)/2.
Proof.
  induction pC as [ | a p IHp]; intros [ | b q] n x; simpl; try field.
  rewrite !eval_add_ /=; ring_simplify.
  rewrite IHp !eval_add_ !eval_scal_ evalCC_cons00_ CCsqr /= Nat.add_succ_r.
  rewrite 2!Rmult_assoc CCeval. 2: lia. rewrite CCeval. 2:lia. 
  replace (S n-n)%nat with 1%nat by lia.
  rewrite C0 Nat.add_succ_l /=. field.
Qed.

Lemma eval_mulCC pC qCC x: evalCC (pmulCC pC qCC) x = evalCC pC x * evalCC qCC x.
Proof. rewrite /evalCC eval_mulCC_ /pmulCC eval_divZ_ eval_add_/= /Rdiv /=. ring. Qed.

(* multiplication of sinus polynoms *)
Lemma evalSS_cons00_ n p x: evalSS_ n (cons00 p) x = evalSS_ n.+2 p x.
Proof. destruct p=>//=. ring. Qed.

Lemma SSeval: forall p n m x,
    (n<=m)%nat -> SS n x * evalSS_ m p x = (evalCC_ (m-n) p x - evalCC_ (m+n) p x)/2.
Proof.
  induction p as [|a p IH]; intros n m x H; simpl.
  - field.
  - ring_simplify. rewrite IH. 2 :lia.
    replace ( _ * SS m x) with (a*(SS n x * SS m x)) by (simpl;ring).
    rewrite SSprod //.
    replace ( m .+1 - n)%nat with ( (m-n) .+1)%nat by lia.
    rewrite Nat.add_succ_l /=. field.
Qed.    

Lemma eval_mulSS_: forall pS qS n x,
    evalSS_ n pS x * evalSS_ n qS x =
    (evalCC_ 0 (mul_minus pS qS) x - evalCC_ (n+n) (mul_plus pS qS) x)/2.
Proof.
  induction pS as [ | a p IHp]; intros [ | b q] n x; simpl; try field.
  rewrite !eval_add_ /=; ring_simplify.
  rewrite IHp !eval_add_ !eval_scal_ !evalCC_cons00_ SSsqr /= Nat.add_succ_r.
  rewrite 2!Rmult_assoc !SSeval. 2: lia. 2:lia. 
  replace (S n-n)%nat with 1%nat by lia.
  rewrite C0 /=. field.
Qed.  

Lemma eval_mulSS pS qS x: evalCC (pmulSS pS qS) x = evalSS pS x * evalSS qS x.
(* pS and qS are polynoms in sinus in which the first index equals to 1 *)
Proof.
  rewrite /evalCC /evalSS eval_mulSS_ /pmulSS eval_divZ_ eval_sub_ evalCC_cons00_ /= /Rdiv /=.
  ring.
Qed.

(* Multiplication of a sinus polynom with a cosinus polynom *)
Lemma SCeval: forall p n m x,
    (n<=m)%nat -> SS n x * evalCC_ m p x = (evalSS_ (m+n) p x - evalSS_ (m-n) p x)/2.
Proof.
  induction p as [|a p IH]; intros n m x H; simpl.
  - field.
  - ring_simplify. rewrite IH. 2 :lia.
    replace ( _ * CC m x) with (a*(SS n x * CC m x)) by (simpl;ring).
    rewrite SCprod //.
    replace ( m .+1 - n)%nat with ( (m-n) .+1)%nat by lia.
    rewrite Nat.add_succ_l /=. field.
Qed.    

Lemma CSeval: forall p n m x,
    (n<=m)%nat -> CC n x * evalSS_ m p x = (evalSS_ (m+n) p x + evalSS_ (m-n) p x)/2. 
Proof.
  induction p as [|a p IH]; intros n m x H; simpl.
  - field.
  - ring_simplify. rewrite IH. 2 :lia.
    replace ( _ * SS m x) with (a*(CC n x * SS m x)) by (simpl;ring).
    rewrite CSprod //.
    replace ( m .+1 - n)%nat with ( (m-n) .+1)%nat by lia.
    rewrite Nat.add_succ_l /=. field.
Qed.

Lemma eval_mulSC_: forall pS qC n x,
    evalSS_ n pS x * evalCC_ n qC x =
    (evalSS_ (n+n) (mul_plus pS qC) x - evalSS_ 0 (mul_minusSC pS qC) x)/2.
Proof.
  induction pS as [ | a p IHp]; intros [ | b q] n x; simpl; try field.
  rewrite !eval_add_ /=; ring_simplify. replace ( a * SS n x * b * CC n x )%R with (a * b * (SS n x * CC n x) )%R by (simpl;ring).
  rewrite IHp. rewrite !eval_sub_ !eval_add_  !eval_scal_ /= !evalSS_cons00_ SCsqr /= Nat.add_succ_r.
  replace ( evalSS_ n .+1 p x * b * CC n x )%R with ( b * (CC n x * evalSS_ n .+1 p x)%R)%R by (simpl;ring).
  rewrite 2!Rmult_assoc. rewrite SCeval. rewrite CSeval. 2: lia. 2:lia.
  
  replace (S n-n)%nat with 1%nat by lia.
  rewrite S0 Rmult_0_r /=. field.
Qed.

Lemma evalSS_0_1 p x: evalSS (tl p) x = evalSS_ 0 p x.
Proof. destruct p. by []. rewrite /= S0 /=; ring. Qed.

Lemma tail_cons0 (p: list R): tl (cons0 p) = p.
Proof. by case p. Qed.

Lemma eval_mulSC' pS qC x: evalSS_ 0 (pmulSC' pS qC) x = evalSS_ 0 pS x * evalCC qC x.
Proof. 
  rewrite /evalCC eval_mulSC_ /pmulSC' eval_divZ_ eval_sub_ /= /Rdiv /=; ring.
Qed.

Lemma eval_mulSC pS qC x: evalSS (pmulSC pS qC) x = evalSS pS x * evalCC qC x.
(* pS is a polynom in sinus in which the first index equals to 1 *)
Proof. 
  by rewrite /pmulSC evalSS_0_1 eval_mulSC' -evalSS_0_1 tail_cons0.
Qed.

(* evaluation of lists after split or merge operations *)

Lemma eval_split_ n p x:
  eval_ n p x =
  if even n then evalCC_ (order n) (evens p) x + evalSS_ (order n .+1) (odds p) x
  else evalCC_ (order n .+1) (odds p) x + evalSS_ (order n) (evens p) x.
Proof.
  elim: p n => [ | a p IHp] n.
  + case even => /=; lra.
  + cbn. fold (@evens R). fold (@odds R). (* BUG: simplification *)
    rewrite IHp /F orderSS Nat.even_succ -Nat.negb_even.
    case even; cbn; lra.
Qed.

Proposition eval_split p x: eval p x = evalCC (evens p) x + evalSS (odds p) x.
Proof. by apply eval_split_. Qed.

Lemma eval_inject n q x:
  eval_ n (inject q) x =
  if even n then evalSS_ (order n).+1 q x
  else evalCC_ (order n) q x.
Proof.
  elim: q n => [ | b q IHq] n /=.
  + by case (even n).
  + rewrite IHq. 
    rewrite Nat.even_succ_succ orderSS /F Nat.even_succ -Nat.negb_even.
    rewrite orderS. case even; simpl; ring. 
Qed.

Lemma eval_merge_ n p q x:
  eval_ n (merge p q) x =
  if even n then evalCC_ (order n) p x + evalSS_ (order n .+1) q x
  else evalSS_ (order n) p x + evalCC_ (order n .+1) q x.
Proof. 
  elim: p q n => [ q n   /= | a p IHp [ | b q ] n  /=].
  + rewrite eval_inject orderS. case even=>/=; ring.
  + rewrite eval_inject /F Nat.even_succ -Nat.negb_even orderS. case even=>/=; ring.
  + rewrite IHp /F Nat.even_succ_succ Nat.even_succ -Nat.negb_even /= !orderSS orderS.
    case even=>/=; ring.
Qed.

Proposition eval_merge p q x: eval (merge p q) x = evalCC p x + evalSS q x.
Proof. by apply eval_merge_. Qed.
  
(* multiplication of Fourier polynoms *)

Theorem eval_mul P Q x: eval (pmul P Q) x = eval P x * eval Q x.
Proof.
  rewrite /pmul (eval_split P) (eval_split Q) eval_merge.
  rewrite eval_add eval_add_ eval_mulCC eval_mulSS 2!eval_mulSC /=. ring.
Qed.

(* Correctness of fast evaluation *)

Lemma fast_evalE_ t P: forall a b,
    even (length P) -> 
    let n := div2 (length P) in
    fast_eval_ (CC 1 t) (SS 1 t) a b P = eval_ 1 (rev2 P) t + a * CC n t + b * SS n t.
Proof.
  induction P as [|x|x y q IH] using list_ind2=>//=a b E.
  + rewrite C0 S0. cbn; ring.
  + move:IH=>->//. set k := div2 _.
    rewrite rev2CC eval_app_ /=. set k' := length _.
    rewrite (Nat.add_comm k')/=. 
    rewrite {3 4}/F orderS !Nat.even_succ Nat.odd_succ -Nat.negb_even.
    rewrite even_length_rev2/= orderSS.
    rewrite order_length_rev2//= -/k. 
    rewrite !Rplus_assoc. f_equal. 
    ring_simplify.
    have D: (k=0 \/ 1<=k)%nat by lia. case: D=>[->|D].
    rewrite C1 C0 S1 S0. cbn; field. 
    rewrite !Rmult_assoc.
    replace (CC 1 t * (y * SS k t))%R with (y * (CC 1 t * SS k t)) by (simpl; ring).
    replace (CC 1 t * (b * SS k t))%R with (b * (CC 1 t * SS k t)) by (simpl; ring).
    rewrite CCprod//SSprod//SCprod//CSprod//.
    rewrite (Nat.add_comm k)/=.
    simpl; field.
Qed.

Lemma eval_rev2_rev2 n P t: eval_ n (rev2 (rev2 P)) t = eval_ n P t.
Proof.
  rewrite rev2invol. case even=>//.
  rewrite eval_app_. cbn. ring.
Qed.

Lemma fast_evalE P x: fast_eval P x = eval P x.
Proof.
  rewrite /fast_eval. case:P=>//h Q.
  rewrite -C1 -S1. rewrite fast_evalE_. 2: apply even_length_rev2.
  rewrite eval_rev2_rev2 /eval/=F0. simpl; ring.
Qed.
    
(** Integration *)

Lemma eval_prim_ o p x: (o >= 1)%nat -> Derive (eval_ (2*o-1) (prim_ (Z.of_nat o) p)) x = eval_ (2*o-1) p x.
Proof.
  move: o. elim/(@list_ind2): p => [ o Ho /= | a o Ho /= | a b p IHp n Hn /= ].
  + apply Derive_const.
    
  + rewrite (@Derive_ext _ (fun x => - a // Z.of_nat o * F (2*o) x)).  
    rewrite Derive_scal. rewrite (@is_derive_unique _ _ (- INR o * F (2*o - 1)%nat x)).
    2: apply F_is_derive_2n => //.
    rewrite /= -INR_IZR_INZ. field. apply not_0_INR; lia.
    simpl; replace ((o + (o + 0) - 1) .+1) with (o+(o+0))%nat. intro t; field.
    rewrite -INR_IZR_INZ. apply not_0_INR; lia. lia.  
 
  + rewrite !Derive_plus. rewrite  !Derive_scal.
    rewrite (@is_derive_unique _ _ ( INR n * F (2*n) x) ) /=.
    rewrite (@is_derive_unique _ _ (- INR n * F ((2*n - 1)) x) ) /=.
    replace ((n+(n+0)-1) .+2)%nat with (2* (n .+1) - 1)%nat by lia.
    replace (n+(n+0)-1) .+1 with (n+(n+0))%nat by lia.
    rewrite -INR_IZR_INZ -Nat2Z.inj_succ IHp. 2: lia.
    field. apply not_0_INR; lia.
    replace (n+(n+0)-1) .+1 with (n+(n+0))%nat by lia.
    apply F_is_derive_2n => //. apply F_is_derive_2nm1 => //.   
    apply ex_derive_scal. apply F_ex_derive. apply eval_ex_derive_.
    apply ex_derive_scal. apply F_ex_derive.
    apply @ex_derive_plus. apply ex_derive_scal. apply F_ex_derive. apply eval_ex_derive_.
Qed.
    
Lemma eval_prim_Derive_ p x: Derive (eval_ 1 (prim_ 1 p)) x = eval_ 1 p x.
Proof. apply (@eval_prim_ 1); lia. Qed.

Lemma eval_integrate p a b: integrate p a b = RInt (eval p) a b.
Proof.
  move: p => [ | x q]. 
  + rewrite /eval /= RInt_const scal_zero_r => //.
  + rewrite /integrate. rewrite 2!fast_evalE /eval /=.
    rewrite RInt_plus. 
  
    erewrite RInt_ext with (f := eval_ 1 q).
    all: swap 1 2. by intros; rewrite -eval_prim_Derive_. 
    rewrite RInt_Derive.
    erewrite RInt_ext with  (g := fun t => x). 
    rewrite RInt_const.   
    simpl. rewrite /plus /scal /= /mult /= !eval_cons0_ /=. ring.
    intros. rewrite F0 /=; ring.
    intros; apply eval_ex_derive_. 
    intros.  eapply continuous_ext.
    intro x1. by rewrite eval_prim_Derive_.
    apply continuity_pt_filterlim, eval_cont_, F_cont.
    apply @ex_RInt_scal. apply ex_RInt_continuous.
    intros. apply continuity_pt_filterlim, F_cont.
    apply ex_RInt_continuous. 
    intros. apply continuity_pt_filterlim, eval_cont_, F_cont.
Qed.    

Lemma eval_range_ x: forall p n, Rabs (eval_ n p x) <= range_ p.
Proof.
  elim => [ | a q IH] n /=.
  + rewrite Rabs_R0; lra.
  + setoid_rewrite Rabs_triang. apply Rplus_le_compat.
    rewrite Rabs_mult. transitivity (Rabs a * 1). 2: simpl; lra.
    apply Rmult_le_compat_l. apply Rabs_pos. 
    generalize (@F_range n x). 
    clear IH; split_Rabs; simpl in *; lra.
    apply IH. 
Qed.

Lemma eval_range {D: R -> Prop} (p: list R) (x: R): D x -> (range p).1 <= eval p x <= (range p).2.
Proof.
  rewrite /range/eval. destruct p as [|a q]=>/=.
  - lra.
  - rewrite F0. move:  (eval_range_ x q 1). simpl. split_Rabs;  lra. 
Qed.

(** ** parametricity of the operations 
    above, we have only specified the instance of the operations on R
    by proving the following parametricity results, we intuitively obtain that they are valid for all instances which are coherent with R (this will be the case with intervals, I).
 *)

Section s.
  Context {R S: Ops1}.
  Variable T: Rel1 R S.
  Notation pT := (list_rel T).

  Lemma revens: forall x y, pT x y -> pT (evens x) (evens y)
  with rodds: forall x y, pT x y -> pT (odds x) (odds y).
  Proof.
    move=>h k. case=>/=; constructor=>//. by apply rodds.
    move=>h k. case=>/=. by constructor. by intros; apply revens.
  Qed.
  Lemma rxrev2: forall x y, pT x y -> forall x' y', pT x' y' -> pT (xrev2 x' x) (xrev2 y' y).
  Proof.
    fix IH 3. 
    destruct 1 as [|????? H]=>//=. 
    destruct H as [|????? H]=>/=; rel.
  Qed.
  Local Hint Resolve rxrev2: rel.
  Lemma rrev2: forall x y, pT x y -> pT (rev2 x) (rev2 y).
  Proof. rel. Qed.
  Lemma rinject: forall x y, pT x y -> pT (inject x) (inject y).
  Proof. induction 1; rel. Qed.
  Local Hint Resolve rinject: rel.
  Lemma rmerge: forall x y, pT x y -> forall x' y', pT x' y' -> pT (merge x x') (merge y y').
  Proof. induction 1. rel. destruct 1; rel. Qed.
  Local Hint Resolve revens rodds rmerge rrev2: rel.
  
  Lemma rmul_minus: forall x y, pT x y -> forall x' y', pT x' y' -> pT (mul_minus x x') (mul_minus y y').
  Proof. induction 1; destruct 1; rel. Qed.
  Lemma rmul_plus: forall x y, pT x y -> forall x' y', pT x' y' -> pT (mul_plus x x') (mul_plus y y').
  Proof. induction 1; destruct 1; rel. Qed.
  Lemma rmul_minusSC: forall x y, pT x y -> forall x' y', pT x' y' -> pT (mul_minusSC x x') (mul_minusSC y y').
  Proof. induction 1; destruct 1; rel. Qed.
  Local Hint Resolve rmul_minus rmul_plus rmul_minusSC: rel.
  Lemma rpmul: forall x y, pT x y -> forall x' y', pT x' y' -> pT (pmul x x') (pmul y y').
  Proof. rel. Qed.

  Lemma rpone: pT pone pone.
  Proof. rel. Qed.
  Lemma rpcos: pT pcos pcos.
  Proof. rel. Qed.
  Lemma rpsin: pT psin psin.
  Proof. rel. Qed.
  Lemma rpcst: forall a b, rel T a b -> pT (pcst a) (pcst b).
  Proof. rel. Qed.
  
  Lemma rfast_eval_: forall P Q, pT P Q -> forall a b , T a b -> forall c d, T c d ->
    forall c1 c2, T c1 c2 -> forall s1 s2, T s1 s2 ->
    rel T (fast_eval_ c1 s1 a c P) (fast_eval_ c2 s2 b d Q).
  Proof.
    fix IH 3. 
    destruct 1 as [|????? H]=>//. 
    destruct H as [|????? H]=>/=; rel.  
  Qed.
  Local Hint Resolve rfast_eval_: rel.
  Lemma rfast_eval: forall P Q, pT P Q -> forall x y, rel T x y -> rel T (fast_eval P x) (fast_eval Q y).
  Proof. destruct 1; rel. Qed.
  
  Lemma rprim_: forall P Q , pT P Q -> forall n , pT (prim_ n P) (prim_ n Q).
  Proof.
    fix IH 3. 
    destruct 1 as [|????? H]=>/=. rel.  
    destruct H as [|????? H]=>/=; rel.  
  Qed.
  Local Hint Resolve rfast_eval rprim_: rel.
  Lemma rintegrate:
    forall P Q, pT P Q -> forall a b, rel T a b -> forall c d , rel T c d ->
    rel T (integrate P a c) (integrate Q b d).
  Proof. destruct 1; rel. Qed.
  Lemma rrange_: forall p q, pT p q -> T (range_ p) (range_ q).
  Proof. induction 1; rel. Qed.
  Local Hint Resolve rrange_: rel.
  Lemma rrange: forall p q, pT p q -> pair_rel T (range p) (range q).
  Proof. destruct 1; rel. Qed.
End s.
Global Hint Resolve rpmul rpone rpcst rfast_eval rprim_ rintegrate rrange_ rrange: rel.


(** ** interpolation  *)
Section i.
 Import interfaces.
 Context {C: Ops1}.
 Variable d: Z.
 Variable f: C -> C.

 Let n := Z.abs d.
 Let sn: Z := 1+n.
 Let sdn: Z := 1+2*n.
 Let csdn: C := fromZ sdn.
 Let twopisdn: C := mulZ 2 pi / csdn.
 
 (** interpolation points *)
 Let point: Z -> C :=
   Zmap.get 0 (
     Zmap.mk (fun i => mulZ i twopisdn) sdn).

 Let map_points g: Z -> C :=
   Zmap.get 0 (
     Zmap.mk (fun i => g (point i)) sdn).

 (** cosine, sine, and values at the interpolation points  *)
 Let cosin := map_points cos.
 Let sinus := map_points sin. 
 Let value := map_points f.

 Let coeff_aux (g: Z -> C) (i: Z): C :=
   Zfold (fun j acc => acc +  value j * g ((i*j) mod sdn)%Z) sdn 0.
      
 Let coeff_cos (i: Z) :=
   (if Z.eqb i 0%Z then ssrfun.id else mulZ 2)
   (coeff_aux cosin i / csdn).

 Let coeff_sin (i: Z) :=
   mulZ 2 (coeff_aux sinus (i+1)) / csdn.

 (* TOTHINK: this returns a list of size [2n+1], while interpolation in Chebyshev returns a polynom of degree [n]. We might wante to divide by two in order to be more uniform. On the other hand a list of Fourier coefficients of length [2n+1] should certainly be called 'of degree n'... *)
 Definition interpolate :=
   merge (Zmap.tolist 0 sn (Zmap.mk coeff_cos sn))
         (Zmap.tolist 0  n (Zmap.mk coeff_sin  n)). 
End i.

(* tests for the above interpolation function *)
(*
Require Import intervals.

Section test.

  Let C := intervals.FOps1.  

  Definition one: C :=  fromZ 1.

  Eval compute in one.

  Definition foo := one / (one + one + one ).

  Eval compute in foo.

  Definition pol: list C := one::one::(one + one)::0::(one + one + one)::[].

  Definition N := 4%Z.

  Check fast_eval pol.
  Check interpolate. 
  (* Eval compute in Zmap.tolist 0 (2*N +1) (@points C N). *)
  (* Eval compute in Zmap.tolist 0 (2*N +1) (@cosin C N). *)
  (* Eval compute in Zmap.tolist 0 (2*N +1) (@sinus C N). *)
  (* Eval compute in Zmap.tolist 0 (2*N +1) (values N (fast_eval pol)). *)
  (* Eval compute in coeff_aux N (Zmap.get 0 (values N (fast_eval pol))) (Zmap.get 0 (@cosin C N)) 0. *)
  (* Eval compute in @coeff_cos C N (fast_eval pol) 0. *)
  Eval vm_compute in pol.       (* [1;1;2;0;3] *)
  Eval vm_compute in interpolate N (fast_eval pol).
 
End test.
 *)

(** packing everything together, we get a basis *)

Definition basis_ops_on (C: Ops1) (lo hi: C): BasisOps_on C := {|
  vectorspace.lo := lo;
  vectorspace.hi := hi;
  vectorspace.beval := @fast_eval C;
  vectorspace.bmul := pmul;
  vectorspace.bone := pone;
  vectorspace.bid := err "id not available in Fourier basis";
  vectorspace.bcos := ret pcos;
  vectorspace.bsin := ret psin;
  vectorspace.bintegrate := integrate;
  vectorspace.brange := Some range;
  vectorspace.interpolate := interpolate;
|}.

Definition basis_ops {N: NBH} (lo hi: II): BasisOps := {|
  BI := basis_ops_on lo hi;
  BF := basis_ops_on (I2F lo) (I2F hi);
|}.

Program Definition basis {N: NBH} (D: Domain):
  Basis (basis_ops dlo dhi) := {|
  TT := F;
  BR := basis_ops_on dlo dhi;
  vectorspace.lohi := dlohi;
  vectorspace.evalE := fast_evalE;
  vectorspace.basis_cont := F_cont;
  vectorspace.eval_mul := eval_mul;
  vectorspace.eval_one := eval_one;
  vectorspace.eval_cos := ep_ret eval_cos;
  vectorspace.eval_sin := ep_ret eval_sin;
  vectorspace.eval_range := eval_range;
  vectorspace.integrateE := eval_integrate;
  vectorspace.rlo := rdlo;
  vectorspace.rhi := rdhi;
  vectorspace.rbmul := @rpmul _ _ (contains (NBH:=N));
  vectorspace.rbone := @rpone _ _ _;
  vectorspace.rbcos := er_ret (@rpcos _ _ _);
  vectorspace.rbsin := er_ret (@rpsin _ _ _);
  vectorspace.rbintegrate := @rintegrate _ _ _;
  vectorspace.rbeval := @rfast_eval _ _ _;
  vectorspace.rbrange := @rrange _ _ _;
|}.
