(** * Syntax for approximable expressions *)

Require Import interfaces errors.

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
Canonical Structure eOps0: Ops0 := {|
  car := expr;
  add := e_add;
  sub := e_sub;
  mul := e_mul;
  zer := e_zer;
  one := e_one;
|}.
Canonical Structure eOps1 := {|
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
Canonical Structure fOps0: Ops0 := {|
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
Canonical Structure fOps1: Ops1 := {|
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

Context {N: NBH} (MM: FunOps). 

(** interpolation degree for divisions and square roots *)
Variable deg: Z.

(** approximation of an expression using intervals / models *)
Fixpoint eSem (e: expr): E II :=
  match e with
  | e_add e f => e_map2 (@add _) (eSem e) (eSem f)
  | e_sub e f => e_map2 (@sub _) (eSem e) (eSem f)
  | e_mul e f => e_map2 (@mul _) (eSem e) (eSem f)
  | e_div e f => e_map2 (@div _) (eSem e) (eSem f)
  | e_sqrt e => e_map (@sqrt _) (eSem e)
  | e_cos e => e_map (@cos _) (eSem e)
  | e_abs e => e_map (@abs _) (eSem e)
  | e_fromZ z => ret (fromZ z)
  | e_pi => ret pi
  | e_eval f x => 
      LET f ::= fSem f IN
      LET x ::= eSem x IN 
      meval f x
  | e_integrate f a b => 
      LET f ::= fSem f IN 
      LET a ::= eSem a IN 
      LET b ::= eSem b IN 
      mintegrate f (Some a) (Some b)
  end
with fSem (e: fxpr): E MM :=
  match e with
  | f_add e f => e_map2 (@add _) (fSem e) (fSem f)
  | f_sub e f => e_map2 (@sub _) (fSem e) (fSem f)
  | f_mul e f => e_map2 (@mul _) (fSem e) (fSem f)
  | f_div e f => LET e ::= fSem e IN LET f ::= fSem f IN mdiv deg e f  (** note the degree used here *)
  | f_sqrt e => LET e ::= fSem e IN msqrt deg e (** note the degree used here *)
  | f_id => ret mid
  | f_cst e => e_map mcst (eSem e)
  | f_trunc e => e_map (mtruncate (Z.to_nat deg)) (fSem e) (** note the degree used here *)
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
  | f_div e f => fcheck e && fcheck f &&
                 match fSem f with
                 | err _ => false
                 | ret f => is_lt 0 (abs (mrange f))
                 end
  | f_id => true
  | f_cst e => echeck e
  | f_trunc e => fcheck e
  | f_sqrt e => fcheck e && 
                 match fSem e with
                 | err _ => false
                 | ret e => is_le 0 (mrange e)
                 end
  end.

Lemma andb_split (a b: bool): a && b -> a /\ b.
Proof. case a; simpl; intuition congruence. Qed.

Definition continuous f := forall x, dom x -> continuity_pt f x. 

Lemma econtains (e: expr): echeck e -> EP' contains (eSem e) (esem e)
with fcontains (f: fxpr): fcheck f -> EP' mcontains (fSem f) (fsem f) /\ continuous (fsem f).
Proof.
  - destruct e; simpl; intro H.
    -- apply andb_split in H as [? ?]. eapply ep_map2. 2,3: apply econtains; eauto. rel. 
    -- apply andb_split in H as [? ?]. eapply ep_map2. 2,3: apply econtains; eauto. rel. 
    -- apply andb_split in H as [? ?]. eapply ep_map2. 2,3: apply econtains; eauto. rel. 
    -- constructor. rel.
    -- constructor. rel. 
    -- apply andb_split in H as [? ?]. eapply ep_map2. 2,3: apply econtains; eauto. rel.
    -- eapply ep_map. 2: apply econtains; eauto. rel.
    -- eapply ep_map. 2: apply econtains; eauto. rel.
    -- eapply ep_map. 2: apply econtains; eauto. rel.
    -- apply andb_split in H as [? ?].
       eapply ep_bind=>[F Ff|]. 2: apply fcontains=>//.  
       eapply ep_bind=>[X Xx|]. 2: apply econtains=>//.  
       now apply rmeval.
    -- do 2 apply andb_split in H as [H ?].
       eapply ep_bind=>[F Ff|]. 2: apply fcontains=>//.  
       eapply ep_bind=>[A Aa|]. 2: apply econtains=>//.  
       eapply ep_bind=>[B Bb|]. 2: apply econtains=>//.  
       apply rmintegrate=>//; try by constructor.
       intros. apply fcontains=>//.
  - destruct f; simpl; intro H.
    -- apply andb_split in H as [H1 H2].
       apply fcontains in H1 as [? ?].
       apply fcontains in H2 as [? ?].
       split. eapply ep_map2; eauto. intros. now apply (radd (r:=mcontains)).
       intros x X. apply continuity_pt_plus; auto. 
    -- apply andb_split in H as [H1 H2].
       apply fcontains in H1 as [? ?].
       apply fcontains in H2 as [? ?].
       split. eapply ep_map2; eauto. intros. now apply (rsub (r:=mcontains)).
       intros x X. apply continuity_pt_minus; auto. 
    -- apply andb_split in H as [H1 H2].
       apply fcontains in H1 as [? ?].
       apply fcontains in H2 as [? ?].
       split. eapply ep_map2; eauto. intros. now apply (rmul (r:=mcontains)).
       intros x X. apply continuity_pt_mult; auto. 
    -- apply andb_split in H as [H' H].
       apply andb_split in H' as [H1 H2].
       apply fcontains in H1 as [? ?].
       apply fcontains in H2 as [Ff2' Cf2].
       split.
       eapply ep_bind=>[F1 Ff1|]. 2: eauto. 
       eapply ep_bind=>[F2 Ff2|]. 2: eauto. 
       now apply rmdiv.
       intros x X. apply continuity_pt_div; auto.
       revert H. case Ff2'=>// F Ff2. case is_ltE=>//H _. 
       assert (0 < Rabs (fsem f2 x)). 
       apply H. apply rzer. now apply rabs, rmrange.
       clear H. split_Rabs; lra.
    -- apply andb_split in H as [H P].
       apply fcontains in H as [? C].
       split.
       eapply ep_bind=>[F Ff|]. 2: eauto. 
       now apply rmsqrt.
       intros x X. apply (continuity_pt_comp (fsem f)). apply C, X. 
       apply continuity_pt_sqrt.
       revert P. case H=>//F Ff. case is_leE=>//P _. apply P. apply rzer.
       now apply rmrange. 
    -- split. constructor. apply rmid. intros x _. apply continuity_pt_id.
    -- split. eapply ep_map. 2: apply econtains=>//. intro. apply rmcst; auto.
       intros x _. now apply continuity_pt_const.
    -- apply fcontains in H as [Ff ?]; split=>//=.
       case Ff; constructor. 
       now apply rmtruncate.
Qed.

(** small corollary, useful to obtain a tactic *)
Lemma bound x a b: echeck x ->
                   (let X := eSem x in
                    match X with ret X => subseteq X a b | err s => False end) ->
                   a <= esem x <= b.
Proof.
  move=>Hx. case (econtains Hx)=>//=X Xx ab.
  eapply subseteqE; eassumption. 
Qed.

End s.
