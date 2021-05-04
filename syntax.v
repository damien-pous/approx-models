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
| e_fromQ: Q -> expr
| e_zer: expr
| e_one: expr
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
  | e_fromQ q => Q2R q
  | e_fromZ z => fromZ z
  | e_zer => 0
  | e_one => 1
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

Lemma VAR: R. exact R0. Qed.

Arguments f_bin [_ _] _ _ _ _ /.
Arguments f_unr [_ _] _ _ _ /.

Ltac ereify e :=
  lazymatch
    eval cbn beta iota delta
         [ROps0 ROps1 f_Ops0 car ops0 zer one add sub mul div sqrt cos abs pi f_bin f_unr fromZ] in e
  with
  | R0 => constr:(e_zer)
  | R1 => constr:(e_one)
  | Rplus ?e ?f => let e:=ereify e in let f:=ereify f in constr:(e_add e f)
  | Rminus ?e ?f => let e:=ereify e in let f:=ereify f in constr:(e_sub e f)
  | Rmult ?e ?f => let e:=ereify e in let f:=ereify f in constr:(e_mul e f)
  | Rdiv ?e ?f => let e:=ereify e in let f:=ereify f in constr:(e_div e f)
  | R_sqrt.sqrt ?e => let e:=ereify e in constr:(e_sqrt e)
  | Rtrigo_def.cos ?e => let e:=ereify e in constr:(e_cos e)
  | Rabs ?e => let e:=ereify e in constr:(e_abs e)
  | Q2R ?q => constr:(e_fromQ q)
  | IZR ?z => constr:(e_fromZ z)
  | Rtrigo1.PI => constr:(e_pi)
  | RInt ?f ?a ?b =>
    let a:=ereify a in
    let b:=ereify b in
    let x:=fresh "x" in
    let fVAR:=constr:(f VAR) in
    let f:=freify fVAR in
    constr:(e_integrate f a b)
  | VAR => fail "variable occurs under an unsupported context"
  | ?e => fail "unrecognised expression:" e
  end
 with freify f :=
    lazymatch
      eval cbn beta iota delta
       [ROps0 ROps1 f_Ops0 car ops0 zer one add sub mul div sqrt cos abs pi f_bin f_unr fromZ]
      in f
    with
  | Rplus ?e ?f => let e:=freify e in let f:=freify f in constr:(f_add e f)
  | Rminus ?e ?f => let e:=freify e in let f:=freify f in constr:(f_sub e f)
  | Rmult ?e ?f => let e:=freify e in let f:=freify f in constr:(f_mul e f)
  | Rdiv ?e ?f => let e:=freify e in let f:=freify f in constr:(f_div e f)
  | R_sqrt.sqrt ?e => let e:=freify e in constr:(f_sqrt e)
  | VAR => constr:(f_id)
  | ?e => let e:=ereify e in constr:(f_cst e)
  end.

(*
Goal True.
  let e := ereify constr:(Rplus R0 R1) in idtac e.
  let e := ereify constr:(42) in idtac e.
  let e := ereify constr:(4.2) in idtac e.
  let e := ereify constr:(0+1: R) in idtac e.
  let e := ereify constr:(RInt (fun z => z) R0 R1) in idtac e.
  let e := ereify constr:(RInt (fun z => R0) R0 R1) in idtac e.
  let e := ereify constr:(RInt (fun z => R0+z) R0 R1) in idtac e.
  let e := ereify constr:(RInt (fun z => R0+z) R0 R1) in idtac e.
  let e := ereify constr:(RInt (@sqrt _) R0 R1) in idtac e.
  let e := ereify constr:(RInt (@sqrt _ + @sqrt _) R0 R1) in idtac e.
  let e := ereify constr:(RInt (fun z => R0+z+cos (1/fromZ 2)) R0 R1) in idtac e.
*)

(** ** static evaluation strategy, where we fix a basis once and for all  *)
Module Static.
Section s.

Context {N: NBH} (MO: ModelOps) lo hi (M: Model MO lo hi). 

(** interpolation degree for divisions, square roots, and truncations *)
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
  | e_fromQ q => ret (fromQ q)
  | e_fromZ z => ret (fromZ z)
  | e_pi => ret pi
  | e_zer => ret 0
  | e_one => ret 1
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
  | f_div e f => LET e ::= fSem e IN LET f ::= fSem f IN mdiv deg e f
  | f_sqrt e => LET e ::= fSem e IN msqrt deg e
  | f_id => ret mid
  | f_cst e => e_map mcst (eSem e)
  | f_trunc e => e_map (mtruncate (Z.to_nat deg)) (fSem e)
  end.

Lemma econtains (e: expr): EP' contains (eSem e) (esem e)
with fcontains (f: fxpr): EP' mcontains (fSem f) (fsem f).
Proof.
  - destruct e; simpl.
    -- eapply ep_map2; try apply econtains; rel. 
    -- eapply ep_map2; try apply econtains; rel. 
    -- eapply ep_map2; try apply econtains; rel. 
    -- constructor. rel. 
    -- constructor. apply rfromQ. 
    -- constructor. apply rzer.
    -- constructor. apply rone.
    -- constructor. rel.
    -- eapply ep_map2; try apply econtains; rel. 
    -- eapply ep_map; try apply econtains; rel. 
    -- eapply ep_map; try apply econtains; rel. 
    -- eapply ep_map; try apply econtains; rel. 
    -- eapply ep_bind=>[F Ff|]. 2: apply fcontains. 
       eapply ep_bind=>[X Xx|]. 2: apply econtains.  
       by apply rmeval.
    -- eapply ep_bind=>[F Ff|]. 2: apply fcontains.  
       eapply ep_bind=>[A Aa|]. 2: apply econtains.  
       eapply ep_bind=>[B Bb|]. 2: apply econtains.  
       apply rmintegrate; rel. 
  - destruct f; simpl.
    -- eapply ep_map2; try apply fcontains. intros. by apply (radd (r:=mcontains)). 
    -- eapply ep_map2; try apply fcontains. intros. by apply (rsub (r:=mcontains)). 
    -- eapply ep_map2; try apply fcontains. intros. by apply (rmul (r:=mcontains)). 
    -- eapply ep_bind=>[F Ff|]. 2: apply fcontains. 
       eapply ep_bind=>[G Gg|]. 2: apply fcontains.  
       by apply rmdiv.
    -- eapply ep_bind=>[F Ff|]. 2: apply fcontains. 
       by apply rmsqrt.
    -- constructor. apply rmid.          
    -- eapply ep_map; try apply econtains. intros. by apply rmcst.          
    -- eapply ep_map; try apply fcontains. intros. by apply rmtruncate.          
Qed.

(** small corollary, useful to obtain a tactic *)
Lemma bound x a b: (let X := eSem x in
                    match X with ret X => subseteq X a b | err s => False end) ->
                   a <= esem x <= b.
Proof.
  case econtains=>//=X Xx ab.
  eapply subseteqE; eassumption. 
Qed.

End s.
Arguments bound {_ _ _ _} _ _ _ _ _.

End Static.


(** ** dynamic evaluation strategy, where we choose the basis according to integral bounds *)
Module Dynamic.
Section s.

Context {N: NBH} (MO: II -> II -> ModelOps) (M: forall D: Domain, Model (MO dlo dhi) dlo dhi).

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
  | e_fromQ q => ret (fromQ q)
  | e_fromZ z => ret (fromZ z)
  | e_pi => ret pi
  | e_zer => ret 0
  | e_one => ret 1
  | e_eval f x => err "evaluation not yet supported in dynamic mode"
      (* LET f ::= fSem f IN *)
      (* LET x ::= eSem x IN  *)
      (* meval f x *)
  | e_integrate f a b => 
      LET a ::= eSem a IN 
      LET b ::= eSem b IN 
      if ~~ is_lt a b then err "dynamic: integral does not yield a valid domain" else
      LET f ::= @fSem (MO a b) f IN 
      mintegrate f None None
  end
with fSem {MO: ModelOps} (e: fxpr): E MM :=
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

Lemma econtains (e: expr): EP' contains (eSem e) (esem e)
with fcontains {MO' a b} {M': Model MO' a b}(f: fxpr): EP' mcontains (fSem f) (fsem f).
Proof.
  - destruct e; simpl.
    -- eapply ep_map2; try apply econtains; rel. 
    -- eapply ep_map2; try apply econtains; rel. 
    -- eapply ep_map2; try apply econtains; rel. 
    -- constructor. rel. 
    -- constructor. apply rfromQ. 
    -- constructor. apply rzer.
    -- constructor. apply rone.
    -- constructor. rel. 
    -- eapply ep_map2; try apply econtains; rel. 
    -- eapply ep_map; try apply econtains; rel. 
    -- eapply ep_map; try apply econtains; rel. 
    -- eapply ep_map; try apply econtains; rel. 
    -- constructor. 
       (* eapply ep_bind=>[F Ff|]. 2: apply fcontains.  *)
       (* eapply ep_bind=>[X Xx|]. 2: apply econtains.   *)
       (* by apply rmeval. *)
    -- eapply ep_bind=>[A Aa|]. 2: apply econtains.  
       eapply ep_bind=>[B Bb|]. 2: apply econtains.
       case_eq (is_lt A B)=>[ab|]. 2: constructor.
       specialize (fcontains _ _ _ (M (DfromI2 Aa Bb ab))).
       eapply ep_bind=>[F Ff|]. 2: apply fcontains.
       eapply rmintegrate; first apply Ff; by constructor. 
  - destruct f; simpl.
    -- eapply ep_map2; try apply fcontains. intros. by apply (radd (r:=mcontains)). 
    -- eapply ep_map2; try apply fcontains. intros. by apply (rsub (r:=mcontains)). 
    -- eapply ep_map2; try apply fcontains. intros. by apply (rmul (r:=mcontains)). 
    -- eapply ep_bind=>[F Ff|]. 2: apply fcontains. 
       eapply ep_bind=>[G Gg|]. 2: apply fcontains.  
       by apply rmdiv.
    -- eapply ep_bind=>[F Ff|]. 2: apply fcontains. 
       by apply rmsqrt.
    -- constructor. apply rmid.          
    -- eapply ep_map; try apply econtains. intros. by apply rmcst.          
    -- eapply ep_map; try apply fcontains. intros. by apply rmtruncate.          
Qed.

(** small corollary, useful to obtain a tactic *)
Lemma bound x a b: (let X := eSem x in
                    match X with ret X => subseteq X a b | err s => False end) ->
                   a <= esem x <= b.
Proof.
  case econtains=>//=X Xx ab.
  eapply subseteqE; eassumption. 
Qed.

End s.
Arguments bound {_ _} _ _ _ _ _.
Arguments fSem {_} _ _ _ _.

End Dynamic.
