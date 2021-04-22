(** * Syntax for approximable expressions *)

Require Import neighborhood.


(* TODO: move FunOps stuff here? *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** syntax for the expressions we know how to approximate *)
Inductive expr :=
| e_add: expr -> expr -> expr
| e_sub: expr -> expr -> expr
| e_mul: expr -> expr -> expr
| e_fromZ: Z -> expr
| e_pi: expr
| e_div: expr -> expr -> expr
| e_sqrt: expr -> expr
| e_cos: expr -> expr
| e_abs: expr -> expr
| e_eval: fxpr -> expr -> expr
| e_integrate: fxpr -> expr -> expr -> expr
with fxpr :=
| f_add: fxpr -> fxpr -> fxpr
| f_sub: fxpr -> fxpr -> fxpr
| f_mul: fxpr -> fxpr -> fxpr
| f_div: fxpr -> fxpr -> fxpr
| f_sqrt: fxpr -> fxpr
| f_id: fxpr
| f_cst: expr -> fxpr
| f_trunc: fxpr -> fxpr.         (* the identity, simply truncates the model *)

(** see expressions as constant functions *)
Coercion f_cst: expr >-> fxpr.

(** declaring structures to get nice notations on expressions *)
Definition e_zer := e_fromZ 0.
Definition e_one := e_fromZ 1.
Canonical Structure eOps0: Ops0 :=
  {|
    car := expr;
    add := e_add;
    sub := e_sub;
    mul := e_mul;
    zer := e_zer;
    one := e_one;
  |}.
Canonical Structure eOps1 :=
  {|
    ops0  := eOps0;
    fromZ := e_fromZ;
    div   := e_div;
    sqrt  := e_sqrt;
    cos   := e_cos;
    abs   := e_abs;
    pi    := e_pi;
  |}.

Definition f_zer := f_cst 0.
Definition f_one := f_cst 1.
Canonical Structure fOps0: Ops0 :=
  {|
    car := fxpr;
    add := f_add;
    sub := f_sub;
    mul := f_mul;
    zer := f_zer;
    one := f_one;
  |}.
Definition f_pi := f_cst pi.
Definition f_fromZ z := f_cst (fromZ z).
(** fake value, not to be used... *)
Definition f_dontuse (f: fxpr): fxpr. exact f. Qed.
Canonical Structure fOps1: Ops1 :=
  {|
    ops0  := fOps0;
    fromZ := f_fromZ;
    div   := f_div;
    sqrt  := f_sqrt;
    pi    := f_pi;
    (** cos, and abs, are not available on functions, only on scalars *)
    cos   := f_dontuse;
    abs   := f_dontuse;
  |}.


(** real number semantics of expressions  *)
Fixpoint esem (e: expr): R :=
  match e with
  | e_add e f => esem e + esem f
  | e_sub e f => esem e - esem f
  | e_mul e f => esem e * esem f
  | e_div e f => esem e / esem f
  | e_sqrt e => sqrt (esem e)
  | e_cos e => cos (esem e)
  | e_abs e => abs (esem e)
  | e_fromZ z => fromZ z
  | e_pi => pi
  | e_eval f x => fsem f (esem x)
  | e_integrate f a b => RInt (fsem f) (esem a) (esem b)
  end
with fsem (e: fxpr) (x: R): R :=
  match e with
  | f_add e f => fsem e x + fsem f x
  | f_sub e f => fsem e x - fsem f x
  | f_mul e f => fsem e x * fsem f x
  | f_div e f => fsem e x / fsem f x
  | f_sqrt e => sqrt (fsem e x)
  | f_id => x
  | f_cst e => esem e
  | f_trunc f => fsem f x
  end.


Section s.

Context {N: NBH} (MM: FunOps II). 

(** interpolation degree for divisions and square roots *)
Variable deg: Z.

(** approximation of an expression using intervals / models *)
Fixpoint eSem (e: expr): II :=
  match e with
  | e_add e f => eSem e + eSem f
  | e_sub e f => eSem e - eSem f
  | e_mul e f => eSem e * eSem f
  | e_div e f => eSem e / eSem f
  | e_sqrt e => sqrt (eSem e)
  | e_cos e => cos (eSem e)
  | e_abs e => abs (eSem e)
  | e_fromZ z => fromZ z
  | e_pi => pi
  | e_eval f x => meval (fSem f) (eSem x)
  | e_integrate f a b => mintegrate (fSem f) (eSem a) (eSem b)
  end
with fSem (e: fxpr): MM :=
  match e with
  | f_add e f => fSem e + fSem f
  | f_sub e f => fSem e - fSem f
  | f_mul e f => fSem e * fSem f
  | f_div e f => mdiv deg (fSem e) (fSem f) (** note the degree used here *)
  | f_sqrt e => msqrt deg (fSem e)          (** note the degree used here *)
  | f_id => mid
  | f_cst e => mcst (eSem e)
  | f_trunc e => mtruncate (Z.to_nat deg) (fSem e)     (** note the degree used here *)
  end.


Notation "a && b" := (if a then b else false).
Fixpoint echeck (e: expr): bool :=
  match e with
  | e_add e f 
  | e_sub e f 
  | e_mul e f 
  | e_div e f => echeck e && echeck f (** note that we do not need to check that f<>0 here !  *)
  | e_sqrt e 
  | e_cos e 
  | e_abs e => echeck e
  | e_fromZ _ | e_pi => true
  | e_eval f x => fcheck f && echeck x
  | e_integrate f a b => fcheck f && echeck a && echeck b
  end
with fcheck (f: fxpr): bool :=
  match f with
  | f_add e f 
  | f_sub e f 
  | f_mul e f => fcheck e && fcheck f
  | f_div e f => fcheck e && fcheck f && is_lt 0 (abs (mrange (fSem f)))
  | f_id => true
  | f_cst e => echeck e
  | f_trunc e => fcheck e
  | f_sqrt e => fcheck e && is_le 0 (mrange (fSem e))
  end.

Lemma andb_split (a b: bool): a && b -> a /\ b.
Proof. case a; simpl; intuition congruence. Qed.

Context {dom: R -> Prop} (mcontains: ValidFunOps contains dom MM).

Definition continuous f := forall x, dom x -> continuity_pt f x. 

Lemma econtains (e: expr): echeck e -> contains (eSem e) (esem e)
with fcontains (f: fxpr): fcheck f -> mcontains (fSem f) (fsem f) /\ continuous (fsem f).
Proof.
  - destruct e; simpl; intro H.
    -- apply andb_split in H as [? ?]; rel. 
    -- apply andb_split in H as [? ?]; rel. 
    -- apply andb_split in H as [? ?]; rel. 
    -- rel.
    -- rel. 
    -- apply andb_split in H as [? ?]; rel.
    -- rel.
    -- rel.
    -- rel.
    -- apply andb_split in H as [? ?]. apply rmeval. apply fcontains=>//. now auto. 
    -- do 2 apply andb_split in H as [H ?].
       apply fcontains in H as [? ?]. 
       apply rmintegrate; eauto. 
  - destruct f; simpl; intro H.
    -- apply andb_split in H as [H1 H2].
       apply fcontains in H1 as [? ?].
       apply fcontains in H2 as [? ?].
       split. now apply (radd (r:=mcontains)).
       intros x X. apply continuity_pt_plus; auto. 
    -- apply andb_split in H as [H1 H2].
       apply fcontains in H1 as [? ?].
       apply fcontains in H2 as [? ?].
       split. now apply (rsub (r:=mcontains)).
       intros x X. apply continuity_pt_minus; auto. 
    -- apply andb_split in H as [H1 H2].
       apply fcontains in H1 as [? ?].
       apply fcontains in H2 as [? ?].
       split. now apply (rmul (r:=mcontains)).
       intros x X. apply continuity_pt_mult; auto. 
    -- apply andb_split in H as [H' H].
       apply andb_split in H' as [H1 H2].
       apply fcontains in H1 as [? ?].
       apply fcontains in H2 as [? ?].
       split. now apply rmdiv.
       intros x X. apply continuity_pt_div; auto.
       revert H. case is_ltE. 2: easy.
       intros H _. assert (0 < Rabs (fsem f2 x)). 
       apply H. apply rzer. now apply rabs, eval_mrange.
       clear H. split_Rabs; lra.
    -- apply andb_split in H as [H P]. apply fcontains in H as [? C].
       split. now apply rmsqrt.
       intros x X. apply (continuity_pt_comp (fsem f)). apply C, X. 
       apply continuity_pt_sqrt.
       revert P. case is_leE=>//P _. apply P. apply rzer.
       now apply eval_mrange. 
    -- split. apply rmid. intros x _. apply continuity_pt_id.
    -- split. apply rmcst; auto. intros x _. now apply continuity_pt_const.
    -- apply fcontains in H as [? ?]; split=>//. now apply rmtruncate.
Qed.

(** small corollary, useful to obtain a tactic *)
Lemma bound x a b: echeck x -> (let X := eSem x in subseteq X a b) -> a <= esem x <= b.
Proof. intros Hx H. exact (subseteqE H (econtains Hx)). Qed.

End s.

