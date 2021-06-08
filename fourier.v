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

Lemma odd_plus n m : even n = false -> even (n+m) = ~~ even m.
Proof.
  rewrite Nat.even_add. intros. rewrite H.
  induction (even m). by []. by [].
Qed.  


Lemma even_minus n m : (n<=m)%nat -> even m -> even (m-n) = even n.
Proof. intros.
       rewrite Nat.even_sub. rewrite H0.
       induction (even n). by []. by []. by []. 
Qed.

Lemma odd_minus n m : (n<=m)%nat -> even m = false -> even (m-n) = ~~ even n.
Proof. intros.
       rewrite Nat.even_sub. rewrite H0.
       induction (even n). by []. by []. by []. 
Qed.

Lemma even_double_ k : even (double k).
Proof. induction k. by []. by rewrite Div2.double_S Nat.even_succ_succ.
Qed.

Lemma odd_double_S k : even ((double k) .+1) = false.
Proof. induction k. by []. by rewrite Div2.double_S Nat.even_succ_succ.
Qed. 

  
Lemma div2_double n : div2 (double n) = n.
Proof.
  induction n. reflexivity.
  by rewrite Div2.double_S /= IHn.
Qed.

Lemma div2_double_add (x a :nat) : div2 ( double x + a ) = (x + div2 a)%nat.
Proof. induction x. by []. by rewrite Div2.double_S /= IHx. Qed.

Lemma div2_double_S x : div2 ( (double x).+1) = x.
Proof.
  rewrite <- Nat.add_1_r. rewrite div2_double_add /=. lia.
Qed.  


Lemma even_double n : even n -> exists k, n = double k.
Proof. intros. exists (div2 n). apply Div2.even_double.
   apply Even.even_equiv. apply Nat.even_spec => //.
Qed.

Lemma odd_double n : even n = false -> exists k, n = (double k) .+1.
Proof.
  intros. exists (div2 n). apply Div2.odd_double.
  apply Even.odd_equiv. apply Nat.odd_spec. by rewrite -Nat.negb_even H. 
Qed. 


Lemma div2_even_plus n m : even n -> div2 (n+m) = (div2 n + div2 m)%nat.
Proof.
  intros. apply even_double in H; destruct H; rewrite H. by rewrite div2_double_add div2_double.    
Qed.

Lemma div2_odd_plus n m : even n = false -> even m = false ->  ((div2 n) + div2 m) .+1%nat = (div2 (n + m)).
Proof.
  intros. apply odd_double in H; destruct H. apply odd_double in H0; destruct H0.
  rewrite H H0.
  replace ((double x) .+1 + (double x0) .+1)%nat with ((double x) + ((double x0) + 2))%nat. rewrite !div2_double_add. 
  rewrite !div2_double_S /=. lia. lia.
Qed.

Lemma double_minus n m : (n<=m)%nat -> (double m - double n)%nat = double (m-n).
Proof. rewrite !Nat.double_twice.  lia.
Qed.


Lemma div2_even_minus n m : (n<=m)%nat -> even n -> even m -> div2 (m-n) = (div2 m - div2 n)%nat.
Proof. 
  intros. apply even_double in H0; destruct H0. apply even_double in H1; destruct H1. rewrite H0 H1.  rewrite !div2_double double_minus => //=. by rewrite div2_double.
  rewrite <- div2_double. rewrite <- (div2_double x). rewrite -H0 -H1. 
  rewrite !Nat.div2_div. apply Nat.div_le_mono => //.
Qed.

Lemma div2_odd_minus n m : (n<=m)%nat -> even m = false ->  div2 (m-n) = (div2 m - div2 n)%nat.
Proof.
  intros.
  apply odd_double in H0; destruct H0; rewrite H0.
  case_eq (even n) => Hn.
  + apply even_double in Hn; destruct Hn. rewrite H1.
    have Hle : (x0 <= x)%nat.
    move: H0 H1; rewrite !Nat.double_twice. lia.
    rewrite div2_double div2_double_S.
    replace ((double x) .+1 - double x0)%nat with (double x - double x0) .+1 => //.
    rewrite double_minus => //. by rewrite div2_double_S. 
    rewrite !Nat.double_twice. lia.
  + apply odd_double in Hn; destruct Hn. rewrite H1.
    rewrite !div2_double_S.
    have Hle : (double x0 <= double x)%nat .
    apply le_S_n. by rewrite -H1 -H0. 
    replace ((double x) .+1 - (double x0) .+1)%nat with ((double x) - (double x0))%nat.
    rewrite double_minus => //. by rewrite div2_double. 
    move: Hle; rewrite !Nat.double_twice. lia.
    lia.
Qed.    

Lemma div2_odd_even_minus n m : (n<=m)%nat -> even m -> even n = false -> (div2 (m-n)) .+1 = (div2 m - div2 n)%nat.
Proof.
  intros.
  apply even_double in H0; destruct H0; rewrite H0.
  apply odd_double in H1; destruct H1; rewrite H1.
  rewrite !div2_double.
  have Hle2 : ( x0 .+1 <=  x)%nat.
  move: H0 H1; rewrite !Nat.double_twice. lia.
  replace  (double x - (double x0) .+1)%nat with ((double x - (double x0.+1)) +1)%nat.
  rewrite double_minus => //. rewrite Nat.add_1_r !div2_double_S. lia.
  rewrite !Nat.double_twice. lia.
Qed.  

Lemma order_double n : order (double n) = n.
Proof. by rewrite /order even_double_ div2_double.
Qed.  

Lemma order_double_S n : order ((double n) .+1) = n .+1. 
Proof. by rewrite /order odd_double_S div2_double_S.
Qed.

Lemma order_succ n : (even n = true -> (order n) .+1 = order n .+1 )/\ (even n = false -> order n = order n .+1) .
Proof.
  induction n.
  split. reflexivity. intros; inversion H. 
  split. intros.
  have Ho : even n = false.
  rewrite Nat.even_succ in H. by rewrite -Nat.negb_odd H.
  destruct IHn. by rewrite -H1 /order /= Ho /=.

  intros.
  have He : even n = true.
  rewrite Nat.even_succ in H. by rewrite -Nat.negb_odd H.
  destruct IHn. by rewrite -H0 /order /= He. 
Qed. 

Lemma order_plus1 n m : even n -> order (n+m) = (order n + order m)%nat.
Proof. intros. rewrite /order even_plus => //.
       case_eq (even m) => Hm.
         by rewrite H div2_even_plus.
         by rewrite H Nat.add_succ_r div2_even_plus.           
Qed.

Lemma order_plus2 n m : even n = false -> even m = false -> order (n+m).+1 = (order n + order m)%nat.
Proof.
  intros. rewrite /order. 
  have Hnm : even (n+m) .+1 = false.
  rewrite Nat.even_succ -Nat.negb_even odd_plus => //. by rewrite H0.
  rewrite Hnm H0 H.
  apply odd_double in Hnm; destruct Hnm.
  apply odd_double in H0; destruct H0.
  apply odd_double in H; destruct H. 
  rewrite H1 H H0 !div2_double_S.
  move: H H1 H0; rewrite !Nat.double_twice. lia.
  Qed.


Lemma order_le_succ n : (order n <= order n .+1)%nat.
Proof.
  case_eq (even n) => Hn.
  apply order_succ in Hn; rewrite <- Hn; by constructor.
  apply order_succ in Hn; rewrite <- Hn; by constructor.
Qed.  

Lemma increasing_order n m : (n<=m)%nat -> (order n <= order m)%nat.
Proof.
  intros. induction m.
    by inversion H.
    inversion H => //.
    apply IHm in H1.
    apply le_trans with (order m). apply H1. apply order_le_succ.
Qed.


Lemma order_minus1 n m : (n<=m)%nat -> (even n = true \/ even m = false -> order (m-n) = (order m - order n)%nat). 
Proof.
  intros. rewrite /order. destruct H0. 

  - case_eq (even m) => Hm.
    + rewrite even_minus => //. rewrite H0. apply div2_even_minus => //.
    + rewrite odd_minus => //. rewrite H0. rewrite div2_odd_minus => //.
      have Hle : ( (div2 n <= div2 m)%nat).
      rewrite !Nat.div2_div. apply Nat.div_le_mono => //. 
      replace (~~ true) with false. lia. by [].
      
  - rewrite div2_odd_minus => //.
    have Hle : ( (div2 n <= div2 m)%nat).
    rewrite !Nat.div2_div. apply Nat.div_le_mono => //. 
    case_eq (even n) => Hn.
    + rewrite odd_minus => //. rewrite H0 Hn.     
      replace (~~ true) with false. lia. by [].
    + rewrite odd_minus => //. rewrite H0 Hn. 
      replace (~~ false) with true. lia. by [].
Qed.

 

Lemma order_minus2 n m : (n<=m)%nat -> (even n =false /\ even m = true -> order (m-n) = (order m - order n) .+1%nat).
Proof.
  intros. rewrite /order. destruct H0. 
  rewrite even_minus => //. rewrite H0 H1 div2_odd_even_minus => //.
  have Hle : ( ((div2 n) .+1 <= div2 m)%nat).
  apply odd_double in H0; destruct H0. apply even_double in H1; destruct H1.
  rewrite H0 H1 div2_double div2_double_S.
  move : H0 H1; rewrite !Nat.double_twice; lia.
  lia.
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
Proof. intros => /=; ring. Qed.

Lemma Radd_plus_minus2 : forall ( a b: R) , a + b + ( a - b ) = a * 2.
Proof. intros => /=; ring. Qed.


Lemma Rmult_div : forall (a x : R) , x <> 0 ->  a * x / x = a. 
Proof. intros => /=; by field. Qed.

Lemma opp_diff : forall (a b:R) , - ( a - b) = b-a.
Proof.
  intros => /= ;ring. Qed.

Lemma opp_opp : forall y x:R ,  y - - x = y + x.
Proof.  intros => /= ;ring. Qed.
  

Lemma form_prod_cos : forall a b , cos a * cos b = (cos (a+b) + cos (a-b))/2.
Proof.
  intros.
  rewrite /= form1 Radd_plus_minus1 Radd_plus_minus2 /= !Rmult_div => //. field.
Qed.  


Lemma form_prod_sin : forall a b, sin a * sin b = (cos (a-b) - cos(a+b))/2.
Proof.
  intros.
  rewrite /= form2.
  replace ((a - b - (a + b))/2)%R with (-b)%R.
  replace ((a - b + (a + b))/2)%R with (a)%R.
 
  rewrite sin_antisym /= Rmult_opp_opp Rmult_assoc Rmult_comm (Rmult_comm (IPR 2) _) Rmult_div => //. rewrite -INR_IPR /=. replace (1 + 1)%R with 2%R. by []. by [].
  field. field. 
Qed.

Lemma form_prod_sin_cos : forall a b, sin a * cos b = (sin (a+b) + sin (a-b))/2.
Proof.
  intros.
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
  rewrite Rmult_plus_distr_r Rmult_minus_distr_r form_prod_sin_cos. 
  replace (INR m * x - INR n * x)%R with (- (INR n * x - INR m * x)%R).
  by rewrite sin_antisym opp_opp (Rplus_comm (INR n * x)%R (INR m * x)%R). 
  ring.
Qed.

Lemma FtoCC : forall k (x : R),  F (double k) x = CC k x.
Proof.
  intros. by rewrite /F even_double_ order_double. Qed.

Lemma FtoSS : forall k (x : R),  F ((double k) .+1) x = SS k .+1 x.
Proof.
  intros. by rewrite /F odd_double_S order_double_S. Qed.

    
Lemma Fprod_cos_cos : forall n m (x : R),
    (n<=m)%nat -> even n -> even m ->
    F n x * F m x = (F (m+n) x + F (m-n) x)/2.
Proof.
  intros.
  apply even_double in H0; destruct H0.
  apply even_double in H1; destruct H1. rewrite H0 H1.
  have Hle : (x0 <= x1)%nat.
    rewrite <- div2_double. rewrite <- (div2_double x0). rewrite -H0 -H1.
    rewrite !Nat.div2_div; apply Nat.div_le_mono => //.

  rewrite -Div2.double_plus double_minus => //.
  rewrite FtoCC FtoCC FtoCC FtoCC => //.
  apply CCprod => //. 
Qed.



Lemma Fprod_sin_sin : forall n m (x : R),
    (n<=m)%nat ->  even n = false -> even m = false ->
    F n x * F m x = (F (m-n) x - F ((m+n) .+2) x)/2.
Proof.
  intros.
  apply odd_double in H0; destruct H0.
  apply odd_double in H1; destruct H1. rewrite H0 H1.
  have Hle : (x0 <= x1)%nat.
  move : H0 H1; rewrite !Nat.double_twice; lia.
   
  replace ((double x1) .+1 + (double x0) .+1) .+2%nat with (double (x1 .+1 + x0 .+1))%nat.
  replace ((double x1) .+1 - (double x0) .+1)%nat with (double (x1 .+1 - x0 .+1))%nat.

  rewrite FtoSS FtoSS FtoCC FtoCC. apply SSprod => //. lia.

  replace (x1 .+1 - x0 .+1)%nat with (x1 - x0)%nat.
  rewrite <- double_minus => //. lia.
  rewrite Div2.double_plus Div2.double_S Div2.double_S. lia.
Qed.


Lemma Fprod_sin_cos : forall n m (x : R),
    (n+2<=m)%nat -> even n = false -> even m ->
    F n x * F m x = (F (m+n) x - F ((m-n) - 2) x)/2.
Proof.
  intros.
  apply odd_double in H0; destruct H0.
  apply even_double in H1; destruct H1. rewrite H0 H1.
  have Hle : (x0 .+2 <= x1)%nat.
    move: H0 H1; rewrite !Nat.double_twice; lia.
   
  replace (double x1 + (double x0) .+1)%nat with ((double (x1 + x0)) .+1).
  replace (double x1 - ((double x0) .+1) - 2 )%nat with ((double (x1 - x0 .+2)) .+1)%nat.

  rewrite FtoSS FtoSS FtoSS FtoCC.

  replace ((x1 + x0) .+1)%nat with (x1 + x0 .+1)%nat.
  replace ((x1 - x0 .+2) .+1)%nat with ( x1 - x0 .+1)%nat.

  apply SCprod => //. lia. lia. lia.
  rewrite !Nat.double_twice.  lia.
  rewrite !Nat.double_twice. lia.
Qed.
  
  
(** Fourier vectors are continuous at every point *)

Lemma CC_cont n x : continuity_pt (CC n) x.
Proof. rewrite /CC. apply (continuity_pt_comp (fun t => INR n *t) (fun t => cos t)). apply continuity_pt_mult. apply continuity_pt_const. by rewrite /constant. 
       apply continuity_pt_id. apply continuity_cos.
Qed.

Lemma SS_cont n x : continuity_pt (SS n) x.
Proof. rewrite /SS. apply (continuity_pt_comp (fun t => INR n *t) (fun t => sin t)). apply continuity_pt_mult. apply continuity_pt_const. by rewrite /constant. 
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
  intros => //=; ring.
Qed.  

  
Lemma Rmult_opp : forall (x:R) , -1 * x =  -x. 
Proof. intros => /=. ring. Qed.


Lemma CC_is_derive n x :  is_derive (CC n) x (- INR n * (SS n x)).
Proof.
  rewrite /CC /SS -Rmult_opp Rmult_comm_assoc Rmult_opp.
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
  rewrite /= F0 Rmult_0_r Rmult_0_l /=. apply @is_derive_const.
  
  rewrite /F.
  case_eq (even n.+1) => He.
  + have Ho : even (n .+2) = false. by rewrite Nat.even_succ -Nat.negb_even He. 
    rewrite Nat.add_1_r /pow_minus_one Ho /dephase He /= -Nat.even_succ_succ Ho.
    rewrite Nat.even_succ_succ in Ho. apply order_succ in Ho. rewrite Ho Rmult_opp.
    apply CC_is_derive.
  + have Ho : even (n .+2). by rewrite Nat.even_succ -Nat.negb_even He.
    rewrite Nat.add_1_r /pow_minus_one Ho /dephase He /= -Nat.even_succ_succ Ho Rmult_1_l.
    apply order_succ in He. rewrite He.
    apply SS_is_derive.
Qed.



(** naive evaluation (defined in vectorspace) 
    eval [a b c] x = a * T 0 x + b * T 1 x + c * T 2 x + 0
 *)
Notation evalCC_ := (eval_ CC).
Notation evalCC := (eval CC).
Notation evalSS_ := (fun n => (eval_ SS (S n))). Check evalSS_. Check evalSS_ (1%nat).
Notation evalSS := (eval_ SS 0).
Notation eval_ := (eval_ F).
Notation eval := (eval F).

(** Definition split/merge splitCC splitSS **)


(*
Lemma eval_evalCCSS : 
 *)

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
  
