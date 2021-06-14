(** * Fourier arithmetic of Fourier basis *)

Require Import vectorspace rescale.
Require Import FSets.FMapPositive Reals.
Require Import Nat ZArith.Zdiv.
Require Import Coq.Program.Wf.
Require Import FunInd Recdef.
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

Lemma order_succ_succ n : order (n .+2) = (order n) .+1.
Proof.
  case_eq (even n) => Hn.
  have HnS :(even n .+1 = false). by rewrite Nat.even_succ -Nat.negb_even Hn.
  apply order_succ in Hn; apply order_succ in HnS; by rewrite -HnS Hn.
  have HnS : even n .+1. by rewrite Nat.even_succ -Nat.negb_even Hn.
  apply order_succ in Hn; apply order_succ in HnS; by rewrite -HnS Hn.
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

Lemma C0 x : CC 0 x = 1.
Proof. by rewrite /CC /= Rmult_0_l cos_0. Qed.         

Lemma S0 x : SS 0 x = 0.
Proof. by rewrite /SS /= Rmult_0_l sin_0. Qed.
  
Lemma F0 x : F 0 x = 1.
Proof. by rewrite /F /= /order /= C0. Qed.        

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

Corollary CCsqr : forall n (x: R),
    CC n x ^ 2 = (CC (n+n) x + 1)/2.
Proof. intros. rewrite (pow_add _ 1 1) pow_1 CCprod // Nat.sub_diag // C0 //. Qed. 

Lemma SSprod : forall n m (x: R),
    (n<=m)%nat ->
    SS n x * SS m x = (CC (m-n) x - CC (m+n) x)/2.
Proof.
  intros.
  rewrite /SS /CC plus_INR minus_INR => //.
  rewrite Rmult_plus_distr_r Rmult_minus_distr_r form_prod_sin. by rewrite (cos_sym (INR n * x - INR m * x)) opp_diff Rplus_comm /=. 
Qed.

Corollary SSsqr : forall n (x: R),
    SS n x ^ 2 = (1 - CC (n+n) x)/2.
Proof. intros. rewrite (pow_add _ 1 1) pow_1 SSprod // Nat.sub_diag // C0 //. Qed.

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

Corollary SCsqr : forall n (x:R),
    SS n x * CC n x = (SS (n+n) x)/2.
Proof. intros. rewrite SCprod // Nat.sub_diag // S0 /=. field. Qed.

Lemma CSprod : forall n m (x:R),
    (n<=m)%nat ->
    CC n x * SS m x = (SS (m+n) x + SS (m-n) x)/2.
Proof.
  intros. rewrite /SS /CC plus_INR minus_INR => //.
  by rewrite /= (Rmult_comm (cos (INR n * x)) (sin (INR m * x))) Rmult_plus_distr_r Rmult_minus_distr_r form_prod_sin_cos.
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

(** Range of Fourier vectors *)

Lemma F_range n x :  -1 <= F n x <= 1.
Proof.
  rewrite /F ; destruct (even n).
  rewrite /CC. apply COS_bound.
  rewrite /SS. apply SIN_bound.
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
    eval [a b c] x = a * F 0 x + b * F 1 x + c * F 2 x + 0
 *)
Notation evalCC_ := (eval_ CC).
Notation evalCC := (eval CC).
Notation evalSS_ := (eval_ SS). 
Notation evalSS := (eval_ SS 1).
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

  Definition cons0 (p: list C) := match p with [] => p | _=>0::p end.
  
  Definition cons00 (p: list C) :=
    match p with [] => p | _=>0::0::p end.


  (** Definition of split/merge splitCC splitSS **)

  Definition cons_left (x: C) (pc: list C * list C) := (x:: (fst pc) , snd pc).

  Definition cons_right (x: C) (pc: list C * list C) := (fst pc , x::(snd pc)).

  Fixpoint split_left (p: list C)  : (list C * list C)  :=
    match p with
    | [] => ([],[])
    | c::q => cons_left c (split_right q)
    end

  with split_right (p: list C) : (list C * list C) :=
    match p with
    | [] => ([],[])
    | c::q => cons_right c (split_left q)
    end.
            
  Definition split_ (p:list C) := split_left p.
  
  Definition splitCC (p:list C) := fst (split_ p).
  
  Definition splitSS (p:list C) := snd (split_ p).
    
  Fixpoint inject_inF (p : list C) : list C :=
    match p with
    | [] => []
    | h::q => 0::h::(inject_inF q)
    end.

  Fixpoint merge_left (pCC : list C) (pSS : list C) : list C :=
    match pCC with
    | [] => inject_inF pSS
    | hC::qC => match pSS with
                | []=> hC::(inject_inF qC)
                | hS::qS => hC::hS::(merge_left qC qS)
                end
    end.

  Fixpoint merge_right (pCC : list C) (pSS : list C) : list C :=
    match pSS with
    | [] => inject_inF pCC
    | hS::qS => match pCC with
                | []=> hS::(inject_inF qS)
                | hC::qC => hS::hC::(merge_right qC qS)
                end
    end.
 
  
  Definition merge := merge_left.
  
  Lemma split_left_right (p: list C) : fst (split_left p) = snd (split_right p) /\ snd (split_left p) = fst (split_right p).
  Proof. elim: p => [ // | a p IHp] /=. inversion IHp. by rewrite H H0. Qed.
  
  Lemma split_lr_fst_cons p a : fst (split_left (a::p)) = a::(fst (split_right p)).
  Proof. by []. Qed.

  Lemma split_lr_snd_cons p a : snd (split_left (a::p)) = (snd (split_right p)).
  Proof. by []. Qed.

  Lemma splitCC_cons (p: list C) (a:C) :  splitCC (a::p) = a::(splitSS p).
  Proof. 
    move: (split_left_right p) => H; inversion H.
      by rewrite  /splitCC /splitSS /split_ /= -H1. 
  Qed.

  Lemma splitSS_cons (p: list C) (a:C) : splitSS (a::p) = splitCC p.
  Proof.
    move: (split_left_right p) => H; inversion H.
      by rewrite  /splitCC /splitSS /split_.
  Qed.

  Lemma merge_left_cons_cons ( p q : list C)  : forall (a b  : C ), merge_left (a::p) (b::q) = a::b::(merge_left p q).
  Proof. by []. Qed.

  Lemma merge_right_cons_cons ( p q : list C)  : forall (a b  : C ), merge_right (b::p) (a::q) = a::b::(merge_right p q).
  Proof. by []. Qed.

  Lemma merge_right_nil q : merge_right q [] = inject_inF q.
  Proof. elim: q => [ // | //]. Qed. 

  Lemma merge_left_right (p q:list C) : merge_left p q = merge_right q p.
  Proof.
    move : q.
    induction p.
    intro q; by rewrite /= merge_right_nil. 
    intro q; move : q => [ // | b q]. by rewrite merge_left_cons_cons merge_right_cons_cons IHp.
  Qed. 

  Lemma merge_cons (p q : list C)  :  forall (a : C), merge (a::p) q = a::merge q p.
  Proof.
    move :q; rewrite /merge. 
    induction p.
    + intros; move : q => [ // | //].
    + intros; move : q => [ // | b q]; by rewrite !merge_left_cons_cons IHp.
  Qed.


  Lemma merge_split (p : list C) : merge (splitCC p) (splitSS p)  = p.
  Proof.
    elim: p => [ // | a p IHp ]; by rewrite splitCC_cons splitSS_cons merge_cons IHp.
  Qed.  



  (** Multiplication *)
  
  Fixpoint mul_minus (p q : list C) : list C :=
    match p,q with
    | [],_ | _,[] => []
    | a :: p', b :: q' => sadd (a*b :: (sadd (sscal a q') (sscal b p'))) (mul_minus p' q')
    end.

  Fixpoint mul_minusSC (p q : list C) : list C :=
    match p,q with
    | [],_ | _,[] => []
    | a :: p', b :: q' => sadd (a*b :: (ssub (sscal a q') (sscal b p'))) (mul_minusSC p' q')
    end.
  
  Fixpoint mul_plus (p q: list C): list C :=
    match p,q with
    | [],_ | _,[] => []
    | a :: p', b :: q' => sadd (a*b :: (sadd (sscal a q') (sscal b p'))) (cons00 (mul_plus p' q'))
    end.

  Definition pmulCC (pCC qCC: list C): list C :=
    sscal (1//2) (sadd (mul_minus pCC qCC) (mul_plus pCC qCC)).

  Definition pmulSS (pSS qSS: list C): list C :=
    sscal (1//2) (ssub (mul_minus pSS qSS) (cons00 (mul_plus pSS qSS))).

  Definition pmulSC' (pSS0 qCC: list C): list C :=
    (* Here only, the polynom in sinus pSS0 has its first index begining in 0 *)  
    sscal (1//2) (ssub (mul_plus pSS0 qCC) (mul_minusSC pSS0 qCC)).

  Definition pmulSC (pSS qCC: list C): list C :=
    tl (pmulSC' (cons0 pSS) qCC).

  Definition pmul (p q : list C): list C :=
    let (pCC,pSS) := split_ p in
    let (qCC,qSS) := split_ q in
    merge (sadd (pmulCC pCC qCC) (pmulSS pSS qSS)) (sadd (pmulSC pSS qCC) (pmulSC qSS pCC)).

  (** Primitive 
   /!\ No periodic primitive for a trigonometric polynom with a non-zero mean value /*\ *)


  (** Evaluation *)

  Fixpoint fast_eval_ a b (P: list C) cost sint :=
    match P with
    | [] => a 
    | [_] => 0
    | a'::b'::Q => fast_eval_ ( (a' + a )* cost + (b' + b) * sint) ((b'+b) * cost - (a' + a) * sint ) Q cost sint
    end.

  Definition fast_eval (P: list C) (x:C) :=
    match P with
    | [] => 0
    | h::Q => h + let (cost , sint ) := (cos x , sin x) in
                  fast_eval_ 0 0
                             (if (even (length Q)) then (rev P) else (cons0 (rev P)))
                             cost sint
    end.
    
  (** domain *)
  Definition lo: C := 0. Check pi.
  Definition hi: C := (fromZ 2)*pi.
  
  (** range on C
    since the [F n] have their range in [-1;1], it suffices to take the sum of the absolute values of   the coefficients. for the constant coefficient, we don't even have to take the absolute value.
   *)
  Definition range_: list C -> C := List.fold_right (fun a x => abs a + x) 0.
  Definition range p: C*C :=
    match p with
    | [] => (0,0)
    | a::q => let r := range_ q in (a-r,a+r)
    end.
  
End ops.

(** ** Correctness of the above polynomial operations, on R *)

Lemma eval_cst a (x: R): eval (pcst a) x = a.
Proof. rewrite /pcst /eval /= F0/=. ring. Qed.

Lemma eval_one (x: R): eval pone x = 1.
Proof. rewrite /pcst /eval /= F0/=. ring. Qed.

(* Multiplication of cosinus polynoms *)
Lemma evalCC_cons00_ n p (x: R): evalCC_ n (cons00 p) x = evalCC_ n.+2 p x.
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

Lemma eval_mulCC_ : forall pCC qCC n x,
    evalCC_ n pCC x * evalCC_ n qCC x =
    (evalCC_ 0 (mul_minus pCC qCC) x + evalCC_ (n+n) (mul_plus pCC qCC) x)/2.
Proof.
  induction pCC as [ | a p IHp]; intros [ | b q] n x; simpl; try field.
  rewrite !eval_add_ /=; ring_simplify.
  rewrite IHp !eval_add_ !eval_scal_ evalCC_cons00_ CCsqr /= Nat.add_succ_r.
  rewrite 2!Rmult_assoc CCeval. 2: lia. rewrite CCeval. 2:lia. 
  replace (S n-n)%nat with 1%nat by lia.
  rewrite C0 Nat.add_succ_l /=. field.
Qed.

Lemma eval_mulCC: forall pCC qCC (x: R), evalCC (pmulCC pCC qCC) x = evalCC pCC x * evalCC qCC x.
Proof. intros. rewrite /evalCC eval_mulCC_ /pmulCC eval_scal_ eval_add_/= /Rdiv /=. ring. Qed.

(* Multiplication of sinus polynoms *)
Lemma evalSS_cons00_ n p (x: R): evalSS_ n (cons00 p) x = evalSS_ n.+2 p x.
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

Lemma eval_mulSS_ : forall pSS qSS n x,
    evalSS_ n pSS x * evalSS_ n qSS x =
    (evalCC_ 0 (mul_minus pSS qSS) x - evalCC_ (n+n) (mul_plus pSS qSS) x)/2.
Proof.
  induction pSS as [ | a p IHp]; intros [ | b q] n x; simpl; try field.
  rewrite !eval_add_ /=; ring_simplify.
  rewrite IHp !eval_add_ !eval_scal_ !evalCC_cons00_ SSsqr /= Nat.add_succ_r.
  rewrite 2!Rmult_assoc !SSeval. 2: lia. 2:lia. 
  replace (S n-n)%nat with 1%nat by lia.
  rewrite C0 /=. field.
Qed.  

Lemma eval_mulSS: forall pSS qSS (x: R), evalCC (pmulSS pSS qSS) x = evalSS pSS x * evalSS qSS x.
(* pSS and qSS are polynoms in sinus in which the first index equals to 1 *)
Proof. intros. rewrite /evalCC /evalSS eval_mulSS_ /pmulSS eval_scal_ eval_sub_ evalCC_cons00_ /= /Rdiv /=. ring. Qed.

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

  
Lemma eval_mulSC_ : forall pSS qCC n x,
    evalSS_ n pSS x * evalCC_ n qCC x =
    (evalSS_ (n+n) (mul_plus pSS qCC) x - evalSS_ 0 (mul_minusSC pSS qCC) x)/2.
Proof.
  induction pSS as [ | a p IHp]; intros [ | b q] n x; simpl; try field.
  rewrite !eval_add_ /=; ring_simplify. replace ( a * SS n x * b * CC n x )%R with (a * b * (SS n x * CC n x) )%R by (simpl;ring).
  rewrite IHp. rewrite !eval_sub_ !eval_add_  !eval_scal_ /= !evalSS_cons00_ SCsqr /= Nat.add_succ_r.
  replace ( evalSS_ n .+1 p x * b * CC n x )%R with ( b * (CC n x * evalSS_ n .+1 p x)%R)%R by (simpl;ring).
  rewrite 2!Rmult_assoc. rewrite SCeval. rewrite CSeval. 2: lia. 2:lia.
  
  replace (S n-n)%nat with 1%nat by lia.
  rewrite S0 Rmult_0_r /=. field.
Qed.

Lemma evalSS_0_1 : forall p x,
    evalSS (tl p) x = evalSS_ 0 p x.
Proof. intros. destruct p as [ | a p ]. by [].
       rewrite /= S0 /=; ring.
Qed.

Lemma tail_cons0 : forall (p:list R) , tl (cons0 p) = p.
Proof. intros. destruct p; by []. Qed.

Lemma eval_mulSC': forall pSS qCC (x: R), evalSS_ 0 (pmulSC' pSS qCC) x = evalSS_ 0 pSS x * evalCC qCC x.
Proof. intros.
       rewrite /evalCC eval_mulSC_ /pmulSC' eval_scal_ eval_sub_ /= /Rdiv /=;ring.
Qed.

Lemma eval_mulSC : forall pSS qCC (x: R), evalSS (pmulSC pSS qCC) x = evalSS pSS x * evalCC qCC x.
(* pSS is a polynom in sinus in which the first index equals to 1 *)
Proof. intros.
         by rewrite /pmulSC evalSS_0_1 eval_mulSC' -evalSS_0_1 tail_cons0.
Qed.


(* Useful lemmas for the evaluation of lists after split or merge operations *)

Lemma eval_split_ n p x :
  eval_ n p x =
  if (even n) then evalCC_ (order n) (splitCC p) x + evalSS_ (order n .+1) (splitSS p) x
  else evalCC_ (order n .+1) (split_ p).2 x + evalSS_ (order n) (split_ p).1 x.
Proof.
  rewrite /splitCC /splitSS /split_.
  elim: p n => [ | a p IHp] n.
  + case (even n) => /=; lra.
  + rewrite split_lr_fst_cons split_lr_snd_cons /=.
    move : IHp => /(_ n.+1) ->.
    move : (split_left_right p) => H. inversion H. rewrite H0 H1 !order_succ_succ.
    move : (order_succ n .+1) => Hn. inversion Hn.
    rewrite Nat.even_succ -Nat.negb_even /F /=.
    destruct (even n) => /=; lra. 
Qed.

Lemma eval_split p x :
  eval p x = evalCC (splitCC p) x + evalSS (splitSS p) x.
Proof. by apply eval_split_. Qed.

Lemma eval_inject_inF_ n q x :
  eval_ n (inject_inF q) x =
  if (even n) then
    evalSS_ (order n) .+1 q x
  else evalCC_ (order n) q x.
Proof.
  elim: q n => [ | b q IHq] n /=.
  + by case (even n).
  + move: IHq => /(_ n .+2) ->.
    rewrite Nat.even_succ_succ order_succ_succ /F Nat.even_succ -Nat.negb_even.
    move: (order_succ n) => [IHe IHo].
  destruct (even n) => /=.
* rewrite -IHe => //; lra.
* rewrite -IHo => //; lra.
Qed.

Lemma eval_inject_inF q x : eval (inject_inF q) x = evalSS q x.
Proof. by apply eval_inject_inF_. Qed.

Lemma eval_merge_ n p q x :
  eval_ n (merge p q) x =
  if (even n) then evalCC_ (order n) p x + evalSS_ (order n .+1) q x
  else evalSS_ (order n) p x + evalCC_ (order n .+1) q x.
Proof. 
  elim: p q n => [ q n   /= | a p IHp [ | b q ] n  /=].
  + rewrite eval_inject_inF_.
    case_eq (even n) => H; apply order_succ in H; rewrite H; lra.
  + rewrite /= eval_inject_inF_ /F Nat.even_succ -Nat.negb_even.
    move: (order_succ n) => [IHe IHo].  
    destruct (even n) => /=.
    rewrite IHe => //; lra.
    rewrite IHo => //; lra.
  + rewrite IHp Nat.even_succ_succ /F.
    rewrite /F Nat.even_succ -Nat.negb_even /= !order_succ_succ. 
    destruct (even n) => /=; ring.
Qed.

Lemma eval_merge p q x :
  eval (merge p q) x = evalCC p x + evalSS q x.
Proof. by apply eval_merge_. Qed.
  
(* Multiplication of Fourier polynoms *)
Theorem eval_mul: forall P Q (x: R), eval (pmul P Q) x = eval P x * eval Q x.
Proof. intros.
       rewrite /pmul (eval_split P) (eval_split Q) /splitCC /splitSS. destruct (split_ P) as (pCC,pSS); destruct (split_ Q) as (qCC, qSS).
       rewrite /= eval_merge eval_add eval_add_ eval_mulCC eval_mulSS 2!eval_mulSC /=. ring.
Qed.



Lemma lohi: lo < hi.
Proof. rewrite /lo /hi /=.  move : PI_RGT_0; lra. Qed.

Lemma eval_range_ x : forall p n, Rabs (eval_ n p x) <= range_ p.
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

Lemma eval_range (p: list R) (x: R) (Hx: lo<=x<=hi): (range p).1 <= eval p x <= (range p).2.
Proof.
  rewrite /range/eval. destruct p as [|a q]=>/=.
  - lra.
  - rewrite F0. move :  (eval_range_ x q 1). simpl. split_Rabs;  lra. 
Qed.

