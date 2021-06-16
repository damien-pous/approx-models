(** * Fourier arithmetic of Fourier basis *)

Require Import vectorspace rescale.
Require Import FSets.FMapPositive Reals.
Require Import ZArith.Zdiv.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** ** Definition of the Fourier Basis and properties *)



Definition F (n:nat) x :=
  match n mod 2 with
  | 0 => cos ( INR (n/2) * x )
  | _ => sin ( INR ((n+1)/2) * x )
  end.

Lemma F0 x : F 0 x = 1.
Proof. unfold F. simpl. rewrite Rmult_0_l. apply cos_0. Qed.

Lemma F1 x : F 1 x = sin x.
Proof. unfold F; simpl. rewrite Rmult_1_l. reflexivity. Qed.

Lemma F2 x : F 2 x = cos x.
Proof. unfold F; simpl. rewrite Rmult_1_l. reflexivity. Qed.

Lemma F_range n x : -1 <= F n x <= 1.
Proof. unfold F. destruct (n mod 2).
       apply COS_bound. apply SIN_bound.
Qed.

(** Fourier vectors are continuous at every point *)
Lemma F_cont n x : continuity_pt (F n) x.
Proof. unfold F; destruct (n mod 2).
       - apply (continuity_pt_comp (fun t => INR (n/2) *t) (fun t => cos t)). apply continuity_pt_mult. apply continuity_pt_const. unfold constant. reflexivity.
         apply continuity_pt_id. apply continuity_cos.
       - apply (continuity_pt_comp (fun t => INR ((n+1)/2) *t) (fun t => sin t)). apply continuity_pt_mult. apply continuity_pt_const. unfold constant. reflexivity.
         apply continuity_pt_id. apply continuity_sin.
Qed.

(** Fourier vectors are derivable at every point *)
Lemma F_ex_derive n x : ex_derive (F n) x.
Proof.
  unfold F; destruct (n mod 2).
  - apply (ex_derive_comp  (fun t => cos t) (fun t => INR (n / 2) * t )).
    exists (- (sin( INR (n/2)* x))).  
    apply is_derive_cos.
    apply ex_derive_mult. apply ex_derive_const. apply ex_derive_id.
  - apply (ex_derive_comp  (fun t => sin t) (fun t => INR ((n+1) / 2) * t )).
    exists ( cos ( INR ((n+1) / 2) * x )).
    apply is_derive_sin.
    apply ex_derive_mult. apply ex_derive_const. apply ex_derive_id.
Qed.

(** relations between Fourier vectors and their derivatives *)

(*
  Lemma F_Derive_cos x n : n mod 2 = 0%nat -> n <> 0%nat -> Derive (F n) x = - ( INR (n/2) * F (n-1) x ).
Proof.
  intros. unfold F. rewrite H.*)


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
