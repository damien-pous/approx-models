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


(*
Lemma div2_double_minus (x a :nat) : (a<= double x)%nat -> div2 ( double x - a ) = (x - div2 a)%nat.
Proof. intros. induction x. by []. rewrite Div2.double_S. Search S. rewrite Nat.succ_1_l. simpl. rewrite /=. IHx. Qed.


Lemma div2_plus2_aux (y a : nat) : (a<=y .+2)%nat -> div2 (y .+2 - a) = div2
 *)

Lemma div2_even_plus n m : even n -> div2 (n+m) = (div2 n + div2 m)%nat.
Proof.
  intros. rewrite (Div2.even_double n). by rewrite div2_double_add div2_double.   
  apply Even.even_equiv. apply Nat.even_spec. apply H. 
Qed.

Lemma minus_n_n (n:nat) : (n - n)%nat = 0%nat.
Proof. induction n. trivial. simpl. apply IHn.
Qed.


Lemma double_minus n m : (n<=m)%nat -> (double m - double n)%nat = double (m-n).
Proof.
  intros. induction m.
  reflexivity. inversion H.        ouble. rewrite Div2.double_S.
*)

  Lemma div2_even_minus n m : (n<=m)%nat -> even n -> even m -> div2 (m-n) = (div2 m - div2 n)%nat.
Proof. 
 intros. rewrite (Div2.even_double m). rewrite (Div2.even_double n).  rewrite div2_double div2_double. Search div2 double.   
 apply Even.even_equiv. apply Nat.even_spec. apply H. 
Qed.
  *)     

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
  intros. rewrite /order. rewrite even_minus. rewrite H0 H1. apply div2_even_minus.
  apply H. apply H0. apply H1. apply H. apply H1.
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


Definition F (n:nat) x :=
  (if even n then cos else sin) ( INR (order n) * x ).


Lemma F0 x : F 0 x = 1.
Proof. by rewrite /F /= Rmult_0_l cos_0. Qed.        

Lemma F1 x : F 1 x = sin x.
Proof. by rewrite /F /= Rmult_1_l. Qed.

Lemma F2 x : F 2 x = cos x.
Proof. by rewrite /F /= Rmult_1_l. Qed.

Lemma Radd_plus_minus1 : forall ( a b: R) ,   a + b - (a - b) = b*2.
Proof. intros. simpl. ring. Qed.

Lemma Radd_plus_minus2 : forall ( a b: R) , a + b + ( a - b ) = a * 2.
Proof. intros. simpl. ring. Qed.


Lemma Rmult_div : forall (a x : R) , x <> 0 ->  a * x / x = a. 
Proof. intros. simpl. by field. Qed.

Lemma opp_diff : forall (a b:R) , - ( a - b) = b-a.
Proof.
  intros. simpl. ring. Qed.
  
  
Lemma form_prod_cos : forall a b , cos a * cos b = (cos (a+b) + cos (a-b))/2.
Proof.
  intros.
  rewrite /= form1 Radd_plus_minus1 Radd_plus_minus2 /= Rmult_div. rewrite Rmult_div. field.
  by []. by [].
Qed.  

Lemma Fprod_cos_cos : forall n m (x : R),
    (n<=m)%nat -> even n -> even m ->
    F n x * F m x = (F (m+n) x + F (m-n) x)/2.
Proof.
  intros.
  rewrite /F even_plus. rewrite even_minus. rewrite order_plus. rewrite order_minus.  rewrite H0 H1.
  Search Rmult Rplus. Search INR. rewrite plus_INR minus_INR /=.
  rewrite Rmult_plus_distr_r Rmult_minus_distr_r form_prod_cos. by rewrite (cos_sym (INR (order n) * x - INR (order m) * x)) opp_diff Rplus_comm /=.
  apply increasing_order. apply H. apply H. apply H0. apply H1. apply H1. apply H. apply H1. apply H1.
Qed.


Lemma F_range n x : -1 <= F n x <= 1.
Proof. rewrite /F; elim: even.
       apply COS_bound. apply SIN_bound.
Qed.



(** Fourier vectors are continuous at every point *)
Lemma F_cont n x : continuity_pt (F n) x.
Proof. rewrite /F; elim: even.
       - apply (continuity_pt_comp (fun t => INR (order n) *t) (fun t => cos t)). apply continuity_pt_mult. apply continuity_pt_const. rewrite /constant. reflexivity.
         apply continuity_pt_id. apply continuity_cos.
       - apply (continuity_pt_comp (fun t => INR (order n) *t) (fun t => sin t)). apply continuity_pt_mult. apply continuity_pt_const. unfold constant. reflexivity.
         apply continuity_pt_id. apply continuity_sin.
Qed.

(** Fourier vectors are derivable at every point *)


Definition pow_minus_one (n:nat) :=
  if even n then 1 else -1.

Definition dephase (n:nat) :nat :=
  match n with
  | 0 => 0
  | S _  => (if even n then pred n else S n) end.

(*
Lemma F_is_derive n (x:R) : is_derive (F n) x (pow_minus_one (n+1) * INR (order n) * (F (dephase n) x)).
Proof.
  destruct n.
  apply is_derive_ext with (fun t => 1). intros; by rewrite F0. Search is_derive. Check Hierarchy.zero. ________________Solution apply (is_derive_const R1 x).___________________________
  simpl. rewrite F0 Rmult_0_r Rmult_0_l /=. apply is_derive_const.
  rewrite /= /F /pow_minus_one /order /dephase /=. rewrite Rmult_0_l. rewrite cos_0 /=.
  rewrite Rmult_0_l.
  + 
 *)

Lemma F_ex_derive n x : ex_derive (F n) x.
Proof.
  rewrite /F; elim: even.
  - apply (ex_derive_comp  (fun t => cos t) (fun t => INR (order n) * t )).
    exists (- (sin( INR (order n)* x))).  
    apply is_derive_cos.
    apply ex_derive_mult. apply ex_derive_const. apply ex_derive_id.
  - apply (ex_derive_comp  (fun t => sin t) (fun t => INR (order n) * t )).
    exists ( cos ( INR (order n) * x )).
    apply is_derive_sin.
    apply ex_derive_mult. apply ex_derive_const. apply ex_derive_id.
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


Lemma F_Derive x n :  Derive (F n) x = (pow_minus_one (n+1) * INR (order n) * (F (dephase n) x)).
Proof.
  destruct n. rewrite <-(Derive_ext (fun=>1)).
  simpl. rewrite F0 Rmult_0_r Rmult_0_l /=. apply Derive_const. intros. by rewrite F0.
  
  unfold F.

  (** case_eq (even n.+1) => H **)
  have H : Nat.Even n \/ Nat.Odd n.
  apply Nat.Even_or_Odd.
  destruct H.
  + have He : even n = true. apply Nat.even_spec; apply H.
    have Ho : even (n .+1) = false. rewrite Nat.even_succ. rewrite <- Nat.negb_even. rewrite He. reflexivity.

    rewrite Ho. unfold dephase. rewrite Ho. rewrite Nat.even_succ_succ. rewrite He. simpl.
    unfold pow_minus_one. rewrite Nat.even_succ. rewrite <- Nat.negb_even. rewrite Nat.add_1_r. rewrite Ho. simpl. apply order_succ in Ho. rewrite <- Ho.

    apply is_derive_unique.
    apply (is_derive_comp (fun t => sin t) (fun t => INR (order n.+1) * t )).
    apply is_derive_sin. rewrite Rmult_1_l /=.
    apply (is_derive_ext (fun t:R => scal t%R (INR (order n .+1)))). 
    intros. apply Rmult_comm. apply is_derive_scal'. 

  + have Ho : even n = false. rewrite <- Nat.negb_odd. Search Nat.odd. apply Nat.odd_spec in H; rewrite H. reflexivity.
    have He : even n .+1 = true. Search Nat.even. rewrite Nat.even_succ. rewrite <- Nat.negb_even. rewrite Ho. reflexivity.

    rewrite He. unfold dephase. rewrite He /=. rewrite Ho.
    unfold pow_minus_one. rewrite Nat.even_succ. rewrite <- Nat.negb_even. rewrite Nat.add_1_r. rewrite He. simpl. apply order_succ in Ho. rewrite Ho.

    apply is_derive_unique. rewrite Rmult_comm_assoc. rewrite Rmult_opp.
    apply (is_derive_comp (fun t => cos t) (fun t => INR (order n.+1) * t )). 
    apply is_derive_cos. 
    apply (is_derive_ext (fun t:R => scal t%R (INR (order n .+1)))). 
    intros. apply Rmult_comm. apply is_derive_scal'. 
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
