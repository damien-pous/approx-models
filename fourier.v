(** * Fourier arithmetic of Fourier basis *)

Require Import vectorspace rescale.
Require Import FSets.FMapPositive Reals.
Require Import Nat ZArith.Zdiv.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** ** Definition of the Fourier Basis and properties *)

Check even.
Check add.
Definition order (n:nat) := 
  if even n then div2 n else add (div2 n) 1.

Definition F (n:nat) x :=
  (if even n then cos else sin) ( INR (order n) * x ).


Lemma F0 x : F 0 x = 1.
Proof. by rewrite /F /= Rmult_0_l cos_0. Qed.        

Lemma F1 x : F 1 x = sin x.
Proof. by rewrite /F /= Rmult_1_l. Qed.

Lemma F2 x : F 2 x = cos x.
Proof. by rewrite /F /= Rmult_1_l. Qed.

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
Print is_derive. Print is_derive_cos.

Definition pow_minus_one (n:nat) :=
  if even n then 1 else -1.

Definition dephase (n:nat) :nat :=
  match n with
  | 0 => 0
  | S _  => (if even n then pred n else S n) end.

(*
Search is_derive. Search R eq.
Lemma equal_is_derive f (g: R->R) : forall y, g y = f y -> forall x l, is_derive f x l -> is_derive g x l.
Proof.
 intros. rewrite H. apply H0.
Qed.
 *)
(*
Lemma F_is_derive n (x:R) : is_derive (F n) x (pow_minus_one (n+1) * INR (order n) * (F (dephase n) x)).
Proof.
  destruct n.
  apply is_derive_ext with (fun t => 1). intros; by rewrite F0. Search is_derive. Check Hierarchy.zero.
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


Lemma F_Derive x n :  Derive (F n) x = (pow_minus_one (n+1) * INR (order n) * (F (dephase n) x)).
Proof.
  destruct n. Search Derive. rewrite <-(Derive_ext (fun=>1)).
  simpl. rewrite F0 Rmult_0_r Rmult_0_l /=. apply Derive_const. intros. by rewrite F0.
  
  unfold F.
  have H : Nat.Even n \/ Nat.Odd n.
  apply Nat.Even_or_Odd.
  destruct H. have He : even n =true. 
  apply Nat.even_spec; apply H.
  have Ho : even (n .+1) = false.
  rewrite Nat.even_succ. rewrite <- Nat.negb_even. rewrite He. reflexivity.
  rewrite Ho. unfold dephase. rewrite Ho. rewrite Nat.even_succ_succ. rewrite He. simpl.
  unfold pow_minus_one. rewrite Nat.even_succ. rewrite <- Nat.negb_even. rewrite Nat.add_1_r. rewrite Ho. simpl.
Search is_derive.
  
  have o : Nat.odd (S n). rewrite Nat.odd_succ. trivial.
  apply Derive_cos.

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



  (** primitive *)
  Fixpoint prim_ (n : nat) (p : list C) : list C :=
    match p with
    | [] => []
    | a::q =>
      match n mod 2 with
        | 
