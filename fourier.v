(** * Fourier arithmetic of Fourier basis *)

Require Import vectorspace rescale.
Require Import FSets.FMapPositive Reals.
Require Import Nat ZArith.Zdiv.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** ** Definition of the Fourier Basis and properties *)



Definition order (n:nat) := 
  if even n then div2 n else  (div2 n).+1.

Lemma even_plus n m : even n ->  even (n+m) = even m.
Proof. 
       rewrite Nat.even_add. intros. rewrite H.
       induction (even m). by []. by []. 
Qed.

Lemma even_minus n m : (n<=m)%nat -> even m -> even (m-n) = even n.
Proof. intros.
       rewrite Nat.even_sub. rewrite H0.
       induction (even n). by []. by []. by []. 
Qed.

Lemma div2_double n : div2 (double n) = n.
Proof.
  induction n. reflexivity.
  by rewrite Div2.double_S /= IHn.
Qed.

Lemma div2_double_add (x a :nat) : div2 ( double x + a ) = (x + div2 a)%nat.
Proof. induction x. by []. by rewrite Div2.double_S /= IHx. Qed.



Lemma div2_even_plus n m : even n -> div2 (n+m) = (div2 n + div2 m)%nat.
Proof.
  intros. rewrite (Div2.even_double n). by rewrite div2_double_add div2_double.   
  apply Even.even_equiv. apply Nat.even_spec. apply H. 
Qed.


Lemma double_minus n m : (n<=m)%nat -> (double m - double n)%nat = double (m-n).
Proof. rewrite Nat.double_twice Nat.double_twice Nat.double_twice.  lia.
Qed.


Lemma div2_even_minus n m : (n<=m)%nat -> even n -> even m -> div2 (m-n) = (div2 m - div2 n)%nat.
Proof. 
  intros. rewrite (Div2.even_double m). rewrite (Div2.even_double n).  rewrite div2_double div2_double double_minus => //=. by rewrite div2_double.  Search Nat.div2 div. rewrite Nat.div2_div Nat.div2_div. apply Nat.div_le_mono => //. 

  apply Even.even_equiv. apply Nat.even_spec. apply H0.
  apply Even.even_equiv. apply Nat.even_spec. apply H1. 
Qed.

      

Lemma order_succ n : (even n = true -> (order n) .+1 = order n .+1 )/\ (even n = false -> order n = order n .+1) .
Proof.
  induction n.
  split. reflexivity. intros; inversion H. 
  split. intros.
  have Ho : even n = false.
  rewrite Nat.even_succ in H. rewrite <- Nat.negb_odd. rewrite H. reflexivity.
  destruct IHn. rewrite <- H1. unfold order.
  simpl. rewrite Ho; simpl. reflexivity. apply Ho.
  intros.
  have He : even n = true.
  rewrite Nat.even_succ in H. rewrite <- Nat.negb_odd. rewrite H. reflexivity.
  destruct IHn. rewrite <- H0. unfold order. simpl. rewrite He. reflexivity.
  apply He.
Qed. 

Lemma order_plus n m : even n -> order (n+m) = (order n + order m)%nat.
Proof. intros. rewrite /order. rewrite even_plus.
       case_eq (even m) => Hm.
         by rewrite H div2_even_plus.
         by rewrite H Nat.add_succ_r div2_even_plus. apply H.
Qed.


Lemma order_minus n m : (n<=m)%nat -> even n -> even m -> order (m-n) = (order m - order n)%nat.
Proof.
  intros. rewrite /order. rewrite even_minus => //. rewrite H0 H1. apply div2_even_minus => //.
Qed.


Lemma order_le_succ n : (order n <= order n .+1)%nat.
Proof.
  case_eq (even n) => Hn.
  apply order_succ in Hn; rewrite <- Hn; by constructor.
  apply order_succ in Hn. rewrite <- Hn. by constructor.
Qed.  

Lemma increasing_order n m : (n<=m)%nat -> (order n <= order m)%nat.
Proof.
  intros. induction m. inversion H. trivial.
  inversion H. trivial. apply IHm in H1. Check le_trans.
  apply le_trans with (order m). apply H1. apply order_le_succ.
Qed.


Definition CC (n:nat) x := cos (INR n * x).

Definition SS (n:nat) x := sin (INR n * x).

Definition F (n:nat) :=
  (if even n then CC else SS) (order n).


Lemma F0 x : F 0 x = 1.
Proof. by rewrite /F /CC /= Rmult_0_l cos_0. Qed.        

Lemma F1 x : F 1 x = sin x.
Proof. by rewrite /F /SS /= Rmult_1_l. Qed.

Lemma F2 x : F 2 x = cos x.
Proof. by rewrite /F /CC /= Rmult_1_l. Qed.

Lemma Radd_plus_minus1 : forall ( a b: R) ,   a + b - (a - b) = b*2.
Proof. intros. simpl. ring. Qed.

Lemma Radd_plus_minus2 : forall ( a b: R) , a + b + ( a - b ) = a * 2.
Proof. intros. simpl. ring. Qed.


Lemma Rmult_div : forall (a x : R) , x <> 0 ->  a * x / x = a. 
Proof. intros. simpl. by field. Qed.

Lemma opp_diff : forall (a b:R) , - ( a - b) = b-a.
Proof.
  intros. simpl. ring. Qed.

Lemma opp_opp : forall y x:R ,  y - - x = y + x.
Proof. intros. simpl. ring.
Qed.  


Lemma form_prod_cos : forall a b , cos a * cos b = (cos (a+b) + cos (a-b))/2.
Proof.
  intros.
  rewrite /= form1 Radd_plus_minus1 Radd_plus_minus2 /= Rmult_div. rewrite Rmult_div. field.
  by []. by [].
Qed.  


Lemma form_prod_sin : forall a b, sin a * sin b = (cos (a-b) - cos(a+b))/2.
Proof.
  intros.
  rewrite /= form2.
  replace (a - b - (a + b))%R with (-2*b)%R.
  replace (a - b + (a + b))%R with (2*a)%R.
  replace (-2 * b / 2)%R with (- b)%R.
  replace (2 * a / 2)%R with a%R.
  rewrite sin_antisym /= Rmult_opp_opp Rmult_assoc Rmult_comm (Rmult_comm (IPR 2) _) Rmult_div. reflexivity. rewrite <- INR_IPR. simpl. replace (1 + 1)%R with 2%R. by []. by [].
  field. field. ring. ring.
Qed.

Lemma form_prod_sin_cos : forall a b, sin a * cos b = (sin (a+b) + sin (a-b))/2.
Proof.
  intros.
  Check form3.
  rewrite /= form3.
  replace ((a + b - (a - b)) / 2)%R with b%R.
  replace ((a + b + (a - b)) / 2)%R with a%R.
  by rewrite Rmult_assoc Rmult_comm (Rmult_comm 2 _) Rmult_div. 
  field. field.
Qed.


Lemma CCprod : forall n m (x : R),
    (n<=m)%nat ->
    CC n x * CC m x = (CC (m+n) x + CC (m-n) x)/2.
Proof.
  intros.
  rewrite /CC plus_INR minus_INR => //=.
  rewrite Rmult_plus_distr_r Rmult_minus_distr_r form_prod_cos. by rewrite (cos_sym (INR n * x - INR m * x)) opp_diff Rplus_comm /=. 
Qed.

Lemma SSprod : forall n m (x: R),
    (n<=m)%nat ->
    SS n x * SS m x = (CC (m-n) x - CC (m+n) x)/2.
Proof.
  intros.
  rewrite /SS /CC plus_INR minus_INR => //.
  rewrite Rmult_plus_distr_r Rmult_minus_distr_r form_prod_sin. by rewrite (cos_sym (INR n * x - INR m * x)) opp_diff Rplus_comm /=. 
Qed.

Lemma SCprod : forall n m (x: R),
    (n<=m)%nat ->
    SS n x * CC m x = (SS (m+n) x - SS (m-n) x)/2.
Proof.
  intros.
  rewrite /SS /CC plus_INR minus_INR => //.
  rewrite Rmult_plus_distr_r Rmult_minus_distr_r form_prod_sin_cos. Check sin_antisym.
  replace (INR m * x - INR n * x)%R with (- (INR n * x - INR m * x)%R).
  by rewrite sin_antisym opp_opp (Rplus_comm (INR n * x)%R (INR m * x)%R). 
  ring.
Qed.
  

Lemma Fprod_cos_cos : forall n m (x : R),
    (n<=m)%nat -> even n -> even m ->
    F n x * F m x = (F (m+n) x + F (m-n) x)/2.
Proof.
  intros.
  rewrite /F even_plus => //. rewrite even_minus => //. rewrite order_plus => //. rewrite order_minus => //.  rewrite H0 H1. apply CCprod. apply increasing_order => //.
Qed.


(*
Lemma Fprod_sin_sin : forall n m (x : R),
    (n<=m)%nat -> ~~ even n -> ~~ even m ->
    F n x * F m x = (F (m+n+1) x - F (m-n) x)/2.
Proof.
  intros.
  rewrite /F. rewrite even_plus.
*)
  
Lemma F_range n x : -1 <= F n x <= 1.
Proof. rewrite /F; elim: even.
       rewrite /CC;apply COS_bound. rewrite /SS;apply SIN_bound.
Qed.



(** Fourier vectors are continuous at every point *)

Lemma CC_cont n x : continuity_pt (CC n) x.
Proof. rewrite /CC. apply (continuity_pt_comp (fun t => INR n *t) (fun t => cos t)). apply continuity_pt_mult. apply continuity_pt_const. rewrite /constant. reflexivity.
         apply continuity_pt_id. apply continuity_cos.
Qed.

Lemma SS_cont n x : continuity_pt (SS n) x.
Proof. rewrite /SS. apply (continuity_pt_comp (fun t => INR n *t) (fun t => sin t)). apply continuity_pt_mult. apply continuity_pt_const. rewrite /constant. reflexivity.
         apply continuity_pt_id. apply continuity_sin.
Qed.

  Lemma F_cont n x : continuity_pt (F n) x.
Proof. rewrite /F; elim: even.
       - apply CC_cont.
       - apply SS_cont.
Qed.

(** Fourier vectors are derivable at every point *)


Definition pow_minus_one (n:nat) :=
  if even n then 1 else -1.

Definition dephase (n:nat) :nat :=
  match n with
  | 0 => 0
  | S _  => (if even n then pred n else S n) end.


Lemma CC_ex_derive n x : ex_derive (CC n) x.
Proof.
  rewrite /CC.
  apply (ex_derive_comp  (fun t => cos t) (fun t => INR n * t )).
    exists (- (sin( INR  n * x))).  
    apply is_derive_cos.
    apply ex_derive_mult. apply ex_derive_const. apply ex_derive_id.
Qed.

Lemma SS_ex_derive n x : ex_derive (SS n) x.
Proof.
  rewrite /SS.
  apply (ex_derive_comp  (fun t => sin t) (fun t => INR n * t )).
    exists (cos( INR  n * x)).  
    apply is_derive_sin.
    apply ex_derive_mult. apply ex_derive_const. apply ex_derive_id.
Qed.


Lemma F_ex_derive n x : ex_derive (F n) x.
Proof.
  rewrite /F; elim: even.
  apply CC_ex_derive. apply SS_ex_derive.
Qed.


(** relations between Fourier vectors and their derivatives *)

Lemma is_derive_scal' : forall (k x : R) , is_derive (fun t => scal t k) x  k.
Proof.
    intros. rewrite <- Rmult_1_l. apply @is_derive_scal_l. apply @is_derive_id.
Qed.

Lemma Rmult_comm_assoc : forall (x y z:R) , x*y*z = y*(x*z).
Proof. 
  intros. rewrite <- Rmult_comm. rewrite <- Rmult_assoc. rewrite <- Rmult_assoc.  rewrite <- Rmult_comm.  rewrite <- (Rmult_comm x z). by rewrite Rmult_assoc. 
Qed.
  
Lemma Rmult_opp : forall (x:R) , -1 * x =  -x. 
Proof. intros. rewrite /=. ring. Qed.


Lemma CC_is_derive n x :  is_derive (CC n) x (-1 * INR n * (SS n x)).
Proof.
  rewrite /CC /SS Rmult_comm_assoc Rmult_opp.
  apply (is_derive_comp (fun t => cos t) (fun t => INR n * t )). 
  apply is_derive_cos. apply (is_derive_ext (fun t:R => scal t%R (INR  n))). 
  intros. apply Rmult_comm. apply is_derive_scal'. 
Qed.

Lemma SS_is_derive n x : is_derive (SS n) x (INR n * (CC n x)).
Proof.
  rewrite /SS /CC.
  apply (is_derive_comp (fun t => sin t) (fun t => INR n * t )).
  apply is_derive_sin. 
  apply (is_derive_ext (fun t:R => scal t%R (INR n))). 
  intros. apply Rmult_comm. apply is_derive_scal'. 
Qed.



Lemma F_is_derive n x :  is_derive (F n) x (pow_minus_one (n+1) * INR (order n) * (F (dephase n) x)).
Proof.
  destruct n. apply is_derive_ext with (fun t => 1). intros; by rewrite F0.
  simpl. rewrite F0 Rmult_0_r Rmult_0_l /=. apply @is_derive_const.
  
  rewrite /F.
  case_eq (even n.+1) => He.
  + have Ho : even (n .+2) = false. rewrite Nat.even_succ. rewrite <- Nat.negb_even. rewrite He. reflexivity.
    rewrite Nat.add_1_r /pow_minus_one Ho /dephase He /=. rewrite <- Nat.even_succ_succ. rewrite Ho.
    rewrite Nat.even_succ_succ in Ho. apply order_succ in Ho. rewrite Ho.
    apply CC_is_derive.
  + have Ho : even (n .+2). rewrite Nat.even_succ. rewrite <- Nat.negb_even. rewrite He. reflexivity.
    rewrite Nat.add_1_r /pow_minus_one Ho /dephase He /=. rewrite <- Nat.even_succ_succ. rewrite Ho Rmult_1_l.
    apply order_succ in He. rewrite He.
    apply SS_is_derive.
Qed.



(** naive evaluation (defined in vectorspace) 
    eval [a b c] x = a * T 0 x + b * T 1 x + c * T 2 x + 0
*)
Notation eval_ := (eval_ F).
Notation eval := (eval F).

(** properties of evaluation: continuity, integrability, and derivability *)

Lemma eval_cont_ P x: forall n, continuity_pt (eval_ n P) x.
Proof.
  induction P as [|a Q IH]; intros n; simpl. 
  + by apply continuity_pt_const. 
  + apply continuity_pt_plus; trivial.
    apply continuity_pt_mult.
      by apply continuity_pt_const.
      by apply F_cont.
Qed.

Lemma eval_cont P x: continuity_pt (eval P) x.
Proof. apply eval_cont_. Qed.

Lemma eval_ex_RInt P a b: ex_RInt (eval P) a b.
Proof.
  apply ex_RInt_Reals_1; case (Rle_dec a b); intro Hab; [ | apply RiemannInt.RiemannInt_P1];
  apply RiemannInt.continuity_implies_RiemannInt; try lra;
    now intros t _; apply eval_cont.
Qed.

Lemma eval_ex_derive_ n P x: ex_derive (eval_ n P) x.
Proof.
  elim: P n => [ | a P IHP] n /=.
  + apply ex_derive_const.
  + auto_derive; repeat split; trivial. apply F_ex_derive.
Qed.

Lemma eval_ex_derive P x : ex_derive (eval P) x.
Proof. apply eval_ex_derive_. Qed.

(** ** Operations on trigonometric polynomials
    This time parametrised by a abstract set C of operations.
    Later, C will be instanciated with reals, floating points, and intervals.
 *)

Section ops.

  Context {C: Ops1}.

  (** constant *)
  Definition pcst a: list C := [a].

  (** one *)
  Definition pone: list C := [1].

  (***** /!\ No identity function -> someting to change in BasisOps_on *)

  (** optimised cons operations, don't know now if it will be useful *)
  Definition cons0 (p: list C) := match p with [] => p | _=>0::p end.
  
  Definition cons00 (p: list C) :=
    match p with [] => p | _=>0::0::p end.


  (** primitive 
   /!\ No periodic primitive for a trigonometric polynom with a non-zero mean value /*\ *)
(*  Fixpoint prim_ (n : nat) (p : list C) : list C :=
    match p with
    | [] => []
    | a::q =>
      match n mod 2 with
        | 
*)
