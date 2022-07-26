(** * Syntax for approximable expressions *)

Require Import String.
Require Import interfaces.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** sorts of expressions we know how to approximate 
    - real numbers
    - functions on closed real intervals
    - (conjunctions/disjunctions) comparison of reals
    - (conjunctions/disjunctions) comparison of models
 *)
Variant sort := REAL | FUN | BOOL | PRED.

(** syntax for the expressions we know how to approximate 
    we use parameterised higher order abstract syntax (PHOAS) in order to have a let..in construct and be able to share subexpressions
    [@term X S] intuitively contains terms of sort [S] with variables in [X]
*)
Inductive term {X: sort -> Type}: sort -> Type :=
(* real expressions *)
| e_add: term REAL -> term REAL -> term REAL
| e_sub: term REAL -> term REAL -> term REAL
| e_mul: term REAL -> term REAL -> term REAL
| e_fromZ: Z -> term REAL
| e_fromQ: Q -> term REAL
| e_zer: term REAL
| e_one: term REAL
| e_pi: term REAL
| e_div: term REAL -> term REAL -> term REAL
| e_sqrt: term REAL -> term REAL
| e_cos: term REAL -> term REAL
| e_sin: term REAL -> term REAL
| e_abs: term REAL -> term REAL
| e_eval: term FUN -> term REAL -> term REAL
| e_integrate: term FUN -> term REAL -> term REAL -> term REAL
(* functional expressions *)
| f_add: term FUN -> term FUN -> term FUN
| f_sub: term FUN -> term FUN -> term FUN
| f_mul: term FUN -> term FUN -> term FUN
| f_div: term FUN -> term FUN -> term FUN
| f_sqrt: term FUN -> term FUN
| f_id: term FUN
| f_cos: term FUN
| f_sin: term FUN
| f_cst: term REAL -> term FUN
| f_trunc: nat -> term FUN -> term FUN         (* the identity, simply truncates the model *)
(* boolean expressions *)
(* TODO: true, false *)
| b_le: term REAL -> term REAL -> term BOOL
| b_ge: term REAL -> term REAL -> term BOOL
| b_lt: term REAL -> term REAL -> term BOOL
| b_ne: term REAL -> term REAL -> term BOOL
    (* need b_ge and not b_gt because Rgt unfolds to Rlt while Rge does not unfold to Rle *)
| b_disj: term BOOL -> term BOOL -> term BOOL
| b_conj: term BOOL -> term BOOL -> term BOOL
| b_forall_models: term REAL -> term REAL -> term PRED -> term BOOL
| b_forall_bisect: term REAL -> term REAL -> (X REAL -> term BOOL) -> term BOOL
(* univariate predicates *)
(* TODO: c_le, c_ge *)
(* TODO: true, false *)
| c_lt: term FUN -> term FUN -> term PRED
| c_ne: term FUN -> term FUN -> term PRED
| c_disj: term PRED -> term PRED -> term PRED
| c_conj: term PRED -> term PRED -> term PRED
| c_cst: term BOOL -> term PRED
| c_forall_bisect: term REAL -> term REAL -> (X REAL -> term PRED) -> term PRED
(* setting the parameters in a subexpression *)
| t_set {S}: prm -> term S -> term S
(* let..in and variable *)
| t_var: forall {S}, X S -> term S
| t_let: forall {S T}, term S -> (X S -> term T) -> term T.
Definition let' {X S T}: @term X S -> (term S -> term T) -> term T :=
  fun a k => t_let a (fun x => k (t_var x)). 
Definition f_trunc' {X} d u: @term X FUN := match d with None => u | Some d => f_trunc d u end.

(** closed terms: they act polymorphically in X *)
Definition Term S := forall X, @term X S.
(** (terms of sort T with a single variable of sort S would be represented by type 
    [forall X, X S -> @term X T]) *)


(** ** real number semantics of expressions  *)
Definition rval S: Type := match S with REAL => R | FUN => (R -> R) | BOOL => Prop | PRED => R -> Prop end.
Fixpoint sem S (t: @term rval S): rval S :=
  match t in term S return rval S with
  | e_add e f => sem e + sem f
  | e_sub e f => sem e - sem f
  | e_mul e f => sem e * sem f
  | e_div e f => sem e / sem f
  | e_sqrt e => sqrt (sem e)
  | e_cos e => cos (sem e)
  | e_sin e => sin (sem e)
  | e_abs e => abs (sem e)
  | e_fromQ q => Q2R q
  | e_fromZ z => fromZ z
  | e_zer => 0
  | e_one => 1
  | e_pi => pi
  | e_eval f x => sem f (sem x)
  | e_integrate f a b => RInt (sem f) (sem a) (sem b)
  | f_add e f => (fun x => sem e x + sem f x)
  | f_sub e f => (fun x => sem e x - sem f x)
  | f_mul e f => (fun x => sem e x * sem f x)
  | f_div e f => (fun x => sem e x / sem f x)
  | f_sqrt e => (fun x => sqrt (sem e x))
  | f_id => id
  | f_cos => cos
  | f_sin => sin
  | f_cst e => (fun _ => sem e)
  | f_trunc _ f => sem f
  | b_le e f => sem e <= sem f
  | b_ge e f => sem e >= sem f
  | b_lt e f => sem e < sem f
  | b_ne e f => sem e <> sem f
  | b_disj b c => sem b \/ sem c
  | b_conj b c => sem b /\ sem c
  | b_forall_models a b k => forall x: R, sem a <= x <= sem b -> sem k x
  | b_forall_bisect a b k => forall x: R, sem a <= x <= sem b -> sem (k x)
  | c_lt f g => fun x => sem f x < sem g x
  | c_ne f g => fun x => sem f x <> sem g x
  | c_disj b c => fun x => sem b x \/ sem c x
  | c_conj b c => fun x => sem b x /\ sem c x
  | c_cst b => fun x => sem b
  | c_forall_bisect a b k => fun x => forall y: R, sem a <= y <= sem b -> sem (k y) x
  | t_set _ _ x => sem x
  | t_var _ x => x
  | t_let _ _ x k => sem (k (sem x))
  end.
Definition sem' S (u: Term S): rval S := sem (u rval).



(** ** reification *)

(* TODO: 
   - maximal sharing using let-ins? [need OCaml?]
   - reify user's let-ins?          [need OCaml?]
*)
Arguments f_bin [_ _] _ _ _ _ /.
Arguments f_unr [_ _] _ _ _ /.
Lemma VAR: R. exact R0. Qed.
Ltac reduce e :=
  eval cbn beta iota delta
       [ROps0 ROps1 f_Ops0 car ops0 zer one add sub mul mul' div sqrt cos sin abs pi f_bin f_unr fromZ]
  in e.
Ltac ereify e :=
  lazymatch e
  with
  | sem' (fun X => ?e) => e
  | R0 => uconstr:(e_zer)
  | R1 => uconstr:(e_one)
  | Rplus ?e ?f => let e:=ereify e in let f:=ereify f in uconstr:(e_add e f)
  | Rminus ?e ?f => let e:=ereify e in let f:=ereify f in uconstr:(e_sub e f)
  | Rmult ?e ?f => let e:=ereify e in let f:=ereify f in uconstr:(e_mul e f)
  | Rdiv ?e ?f => let e:=ereify e in let f:=ereify f in uconstr:(e_div e f)
  | R_sqrt.sqrt ?e => let e:=ereify e in uconstr:(e_sqrt e)
  | Rtrigo_def.cos ?e => let e:=ereify e in uconstr:(e_cos e)
  | Rtrigo_def.sin ?e => let e:=ereify e in uconstr:(e_sin e)
  | Rabs ?e => let e:=ereify e in uconstr:(e_abs e)
  | set ?p ?e => let e:=ereify e in uconstr:(t_set p e)
  | Q2R ?q => uconstr:(e_fromQ q)
  | IZR ?z => uconstr:(e_fromZ z)
  | Rtrigo1.PI => uconstr:(e_pi)
  | RInt ?f ?a ?b =>
    let a:=ereify a in
    let b:=ereify b in
    let fVAR:=reduce (f VAR) in
    let f:=freify fVAR in
    uconstr:(e_integrate f a b)
  | VAR => fail "variable occurs under an unsupported context"
  | ?e => fail "unrecognised expression:" e
  end
 with freify f :=
    lazymatch f with
  | sem' (fun X => ?e) VAR => e
  | Rplus ?e ?f => let e:=freify e in let f:=freify f in uconstr:(f_add e f)
  | Rminus ?e ?f => let e:=freify e in let f:=freify f in uconstr:(f_sub e f)
  | Rmult ?e ?f => let e:=freify e in let f:=freify f in uconstr:(f_mul e f)
  | Rmult' ?d ?e ?f => let e:=freify e in let f:=freify f in uconstr:(f_trunc d (f_mul e f))
  | Rtruncate ?d ?e => let e:=freify e in uconstr:(f_trunc d e)
  | Rdiv ?e ?f => let e:=freify e in let f:=freify f in uconstr:(f_div e f)
  | R_sqrt.sqrt ?e => let e:=freify e in uconstr:(f_sqrt e)
  | set ?p ?e => let e:=freify e in uconstr:(t_set p e)
  | Rtrigo_def.cos VAR => uconstr:(f_cos)
  | Rtrigo_def.sin VAR => uconstr:(f_sin)
  | VAR => uconstr:(f_id)
  | ?e => let e:=ereify e in uconstr:(f_cst e)
    end.
Ltac breify b :=
  lazymatch b with
  | sem' (fun X => ?e) => e
  | ?e <= ?f <= ?g =>
    let e:=ereify e in let f:=ereify f in let g:=ereify g in
    uconstr:(let' f (fun x => b_conj (b_le e x) (b_le x g)))
    (* TOREPORT: weird bug if we alpha-rename x into f above (see DAGGER below) *)
  | ?e <= ?f < ?g =>
    let e:=ereify e in let f:=ereify f in let g:=ereify g in
    uconstr:(let' f (fun x => b_conj (b_le e x) (b_lt x g)))
  | ?e < ?f <= ?g =>
    let e:=ereify e in let f:=ereify f in let g:=ereify g in
    uconstr:(let' f (fun x => b_conj (b_lt e x) (b_le x g)))
  | ?e < ?f <= ?g =>
    let e:=ereify e in let f:=ereify f in let g:=ereify g in
    uconstr:(let' f (fun x => b_conj (b_lt e x) (b_lt x g)))
  | Rle ?e ?f => let e:=ereify e in let f:=ereify f in uconstr:(b_le e f)
  | Rge ?e ?f => let e:=ereify e in let f:=ereify f in uconstr:(b_ge e f)
  | Rlt ?e ?f => let e:=ereify e in let f:=ereify f in uconstr:(b_lt e f)
  | Rgt ?f ?e => let e:=ereify e in let f:=ereify f in uconstr:(b_lt e f)
  | ?e <> ?f => let e:=ereify e in let f:=ereify f in uconstr:(b_ne e f)
  | ?b /\ ?c => let b:=breify b in let c:=breify c in uconstr:(b_conj b c)
  | ?b \/ ?c => let b:=breify b in let c:=breify c in uconstr:(b_disj b c)
  | set ?p ?e => let e:=breify e in uconstr:(t_set p e)
  | forall x, ?a <= x <= ?b -> @?p x =>
    let a:=ereify a in
    let b:=ereify b in
    let pVAR:=reduce (p VAR) in
    let p:=creify pVAR in
    uconstr:(b_forall_models a b p)
  | ?e => fail "unrecognised propositional expression:" e
  end
    with creify b :=
  lazymatch b with
  | sem' (fun X => ?e) VAR => e
  | ?e < ?f < ?g =>
    let e:=freify e in let f:=freify f in let g:=freify g in
    uconstr:(let' f (fun x => c_conj (c_lt e x) (c_lt x g)))
  | Rlt ?e ?f => let e:=freify e in let f:=freify f in uconstr:(c_lt e f)
  | ?e <> ?f => let e:=freify e in let f:=freify f in uconstr:(c_ne e f)
  | ?b /\ ?c => let b:=creify b in let c:=creify c in uconstr:(c_conj b c)
  | ?b \/ ?c => let b:=creify b in let c:=creify c in uconstr:(c_disj b c)
  | ?e => let e:=breify e in uconstr:(c_cst e)
  | set ?p ?e => let e:=creify e in uconstr:(t_set p e)
  end.
Ltac reify_real e :=
  let e := reduce e in
  let e := ereify e in
  constr:((fun X => e): Term REAL).
Ltac reify_fun e :=
  let e := reduce (e VAR) in
  let e := freify e in
  constr:((fun X => e): Term FUN).
Ltac reify_prop e :=
  let e := reduce e in
  let e := breify e in
  constr:((fun X => e): Term BOOL).
Ltac reify_pred e :=
  let e := reduce e in
  let e := creify e in
  constr:((fun X => e): Term PRED).

(* tests for the above reification tatics *)
(*
Goal True.
  let e := reify_real constr:(Rplus R0 R1) in pose e.
  let e := reify_real constr:(42) in pose e.
  let e := reify_real constr:(4.2) in pose e.
  let e := reify_real constr:(0+1: R) in pose e.
  let e := reify_real constr:(RInt (fun z => z) R0 R1) in pose e.
  let e := reify_real constr:(RInt (fun z => R0) R0 R1) in pose e.
  let e := reify_real constr:(RInt (fun z => R0+z) R0 R1) in pose e.
  let e := reify_real constr:(RInt (fun z => R0+z) R0 R1) in pose e.
  let e := reify_real constr:(RInt (@sqrt _) R0 R1) in pose e.
  let e := reify_real constr:(RInt (@sqrt _ + @sqrt _) R0 R1) in pose e.
  let e := reify_real constr:(RInt (@sqrt _ *[4] @sqrt _) R0 R1) in pose e.
  let e := reify_real constr:(RInt (fun x => sqrt x *[4] sqrt x) R0 R1) in pose e.
  let e := reify_real constr:(RInt (fun x => sqrt x *[4] (set (degree 5) (sqrt x))) R0 R1) in pose e.
  let e := reify_real constr:(RInt (fun x => sqrt x *[4] (Rtruncate 5 (sqrt x))) R0 R1) in pose e.
  let e := reify_real constr:(RInt (fun z => R0+z+cos (1/fromZ 2)) R0 R1) in pose e.
  let f := reify_fun  constr:(fun x: R => x * sqrt x) in pose f.
  let b := reify_prop constr:(1/2 <= 3 <= 1/2) in pose b. (* DAGGER: double check *)
  let b := reify_prop constr:(4 <= 5 <= 6) in pose b.
  let b := reify_prop constr:(4 < 5 /\ 3 <= RInt id 3.3 4.4 <= 18.9) in pose b.
  let b := reify_prop constr:(4 >= 5) in pose b. 
  let b := reify_prop constr:(forall x, 4 <= x <= 5 -> x*x < sqrt x) in pose b.
  let b := reify_prop constr:(set (degree 3) (1/2 <= 3) /\ set (depth 4) (0 <= 1/2)) in pose b.
  let b := reify_prop constr:(forall x, 2<=x<=cos 2 -> 1/x <> sqrt x) in pose b. 
  Fail let b := reify_prop constr:(forall x, 2<=x<=cos x -> 1/x <> sqrt x) in pose b. 
  exact I. 
Qed.
 *)
(* reifying under lambdas?
Ltac r e := match eval hnf in e with forall x: R, @?P x => r (P (VAR)) | ?x = ?y => idtac x y | _ => idtac e end.
Goal True.
r (forall x: R, x=x).
Abort.
*)

(** ** parametricity relation for terms. *)
(** This inductive relation is required because of our PHOAS encoding of the syntax.
    We use it to be able to proceed by induction on terms when proving correctness of the interval/model semantics below. *)
(* TOTHINK, generate it using coq-paramcoq?

   Declare ML Module "paramcoq".
   Parametricity Recursive term. 

   problem is that this generates useless reformulations of [eq] for the types used in term (sort, Z, Q)
  *)
Inductive trel X Y (R: forall S, X S -> Y S -> Prop): forall S, @term X S -> @term Y S -> Prop :=
| re_add: forall x y, trel R x y -> forall x' y', trel R x' y' -> trel R (e_add x x') (e_add y y')
| re_sub: forall x y, trel R x y -> forall x' y', trel R x' y' -> trel R (e_sub x x') (e_sub y y')
| re_mul: forall x y, trel R x y -> forall x' y', trel R x' y' -> trel R (e_mul x x') (e_mul y y')
| re_fromZ: forall z, trel R (e_fromZ z) (e_fromZ z)
| re_fromQ: forall q, trel R (e_fromQ q) (e_fromQ q)
| re_zer: trel R e_zer e_zer
| re_one: trel R e_one e_one
| re_pi: trel R e_pi e_pi
| re_div: forall x y, trel R x y -> forall x' y', trel R x' y' -> trel R (e_div x x') (e_div y y')
| re_sqrt: forall x y, trel R x y -> trel R (e_sqrt x) (e_sqrt y)
| re_cos: forall x y, trel R x y -> trel R (e_cos x) (e_cos y)
| re_sin: forall x y, trel R x y -> trel R (e_sin x) (e_sin y)
| re_abs: forall x y, trel R x y -> trel R (e_abs x) (e_abs y)
| re_eval: forall x y, trel R x y -> forall x' y', trel R x' y' -> trel R (e_eval x x') (e_eval y y')
| re_integrate: forall f g, trel R f g -> forall x y, trel R x y -> forall x' y', trel R x' y' -> trel R (e_integrate f x x') (e_integrate g y y')
| rf_add: forall x y, trel R x y -> forall x' y', trel R x' y' -> trel R (f_add x x') (f_add y y')
| rf_sub: forall x y, trel R x y -> forall x' y', trel R x' y' -> trel R (f_sub x x') (f_sub y y')
| rf_mul: forall x y, trel R x y -> forall x' y', trel R x' y' -> trel R (f_mul x x') (f_mul y y')
| rf_div: forall x y, trel R x y -> forall x' y', trel R x' y' -> trel R (f_div x x') (f_div y y')
| rf_sqrt: forall x y, trel R x y -> trel R (f_sqrt x) (f_sqrt y)
| rf_id: trel R f_id f_id
| rf_cos: trel R f_cos f_cos
| rf_sin: trel R f_sin f_sin
| rf_cst: forall x y, trel R x y -> trel R (f_cst x) (f_cst y)
| rf_trunc: forall d x y, trel R x y -> trel R (f_trunc d x) (f_trunc d y)
| rb_le: forall x y, trel R x y -> forall x' y', trel R x' y' -> trel R (b_le x x') (b_le y y')
| rb_ge: forall x y, trel R x y -> forall x' y', trel R x' y' -> trel R (b_ge x x') (b_ge y y')
| rb_lt: forall x y, trel R x y -> forall x' y', trel R x' y' -> trel R (b_lt x x') (b_lt y y')
| rb_ne: forall x y, trel R x y -> forall x' y', trel R x' y' -> trel R (b_ne x x') (b_ne y y')
| rb_disj: forall x y, trel R x y -> forall x' y', trel R x' y' -> trel R (b_disj x x') (b_disj y y')
| rb_conj: forall x y, trel R x y -> forall x' y', trel R x' y' -> trel R (b_conj x x') (b_conj y y')
| rb_forall_models: forall x y, trel R x y -> forall x' y', trel R x' y' -> forall h k, trel R h k -> 
                           trel R (b_forall_models x x' h) (b_forall_models y y' k)
| rb_forall_bisect: forall x y, trel R x y -> forall x' y', trel R x' y' -> 
                    forall h k, (forall a b, R REAL a b -> trel R (h a) (k b)) -> 
                           trel R (b_forall_bisect x x' h) (b_forall_bisect y y' k)
| rc_lt: forall f g, trel R f g -> forall h k, trel R h k -> trel R (c_lt f h) (c_lt g k)
| rc_ne: forall f g, trel R f g -> forall h k, trel R h k -> trel R (c_ne f h) (c_ne g k)
| rc_disj: forall x y, trel R x y -> forall x' y', trel R x' y' -> trel R (c_disj x x') (c_disj y y')
| rc_conj: forall x y, trel R x y -> forall x' y', trel R x' y' -> trel R (c_conj x x') (c_conj y y')
| rc_cst: forall x y, trel R x y -> trel R (c_cst x) (c_cst y)
| rc_forall_bisect: forall x y, trel R x y -> forall x' y', trel R x' y' -> 
                    forall h k, (forall a b, R REAL a b -> trel R (h a) (k b)) -> 
                           trel R (c_forall_bisect x x' h) (c_forall_bisect y y' k)
| rt_set: forall p S x y, trel R x y -> trel R (@t_set _ S p x) (@t_set _ S p y)
| rt_var: forall S x y, R S x y -> trel R (t_var x) (t_var y)
| rt_let: forall S T x y h k, trel R x y -> (forall a b, R S a b -> trel R (h a) (k b)) -> trel R (t_let x h) (@t_let _ _ T y k).

(** all (closed) terms are parametric in the following sense, 
    but this cannot be proved once and for all. Given a concrete closed term, it is however trivial to prove its parametricity (tactic: repeat (constructor; auto)) 
    once a closed term has been proved parametric, one can prove facts by induction on this term
    (see lemmas [Static.correct] and [Dynamic.correct] below) *)
Definition parametric S (u: Term S) :=
  forall X Y (R: forall S, X S -> Y S -> Prop), trel R (u X) (u Y).


(** ** static evaluation function *)
(** where we fix a basis once and for all  *)
Module Static.
Section s.

Context {N: NBH} (MO: ModelOps) (D: Domain) (M: Model MO dlo dhi). 


(** interpretation of expressions using intervals / models / booleans *)
Definition sval S :=
  match S with
  | REAL => E II
  | FUN => E MM
  | BOOL => E bool
  | PRED => E bool
  end.
Fixpoint Sem (p: prms) S (t: @term sval S): sval S :=
  match t in term S return sval S with
  | e_add e f => e_map2 (@add _) (Sem p e) (Sem p f)
  | e_sub e f => e_map2 (@sub _) (Sem p e) (Sem p f)
  | e_mul e f => e_map2 (@mul _) (Sem p e) (Sem p f)
  | e_div e f => e_map2 (@div _) (Sem p e) (Sem p f)
  | e_sqrt e => e_map (@sqrt _) (Sem p e)
  | e_cos e => e_map (@cos _) (Sem p e)
  | e_sin e => e_map (@sin _) (Sem p e)
  | e_abs e => e_map (@abs _) (Sem p e)
  | e_fromQ q => ret (fromQ q)
  | e_fromZ z => ret (fromZ z)
  | e_pi => ret pi
  | e_zer => ret 0
  | e_one => ret 1
  | e_eval f x => 
      LET f ::= Sem p f IN
      LET x ::= Sem p x IN 
      meval f x
  | e_integrate f a b => 
      LET f ::= Sem p f IN 
      LET a ::= Sem p a IN 
      LET b ::= Sem p b IN 
      mintegrate f (Some a) (Some b)
  | f_add e f => e_map2 (@add _) (Sem p e) (Sem p f)
  | f_sub e f => e_map2 (@sub _) (Sem p e) (Sem p f)
  | f_mul e f => e_map2 (@mul _) (Sem p e) (Sem p f)
  | f_div e f => LET e ::= Sem p e IN LET f ::= Sem p f IN mdiv (p_deg p) (p_trunc p) e f
  | f_sqrt e => LET e ::= Sem p e IN msqrt (p_deg p) (p_trunc p) e
  | f_id => mid
  | f_cos => mcos
  | f_sin => msin
  | f_cst e => e_map mcst (Sem p e)
  | f_trunc d e => e_map (mtruncate d) (Sem p e)
  | b_le e f => e_map2 is_le (Sem p e) (Sem p f)
  | b_ge e f => e_map2 is_ge (Sem p e) (Sem p f)
  | b_lt e f => e_map2 is_lt (Sem p e) (Sem p f)
  | b_ne e f => e_map2 is_ne (Sem p e) (Sem p f)
  | b_disj b c | c_disj b c => Eor (Sem p b) (fun _ => Sem p c)
  | b_conj b c | c_conj b c => Eand (Sem p b) (fun _ => Sem p c)
  | c_lt f g => LET f ::= Sem p f IN LET g ::= Sem p g IN mlt (p_deg p) f g
  | c_ne f g => e_map2 (mne (p_deg p)) (Sem p f) (Sem p g)
  | c_cst b => Sem p b
  | c_forall_bisect a b k 
  | b_forall_bisect a b k => 
      LET a ::= Sem p a IN
      LET b ::= Sem p b IN
      bisect (p_depth p) (fun x => Sem p (k (ret x))) (interval a b)
  | b_forall_models a b k => 
      LET a ::= Sem p a IN
      LET b ::= Sem p b IN
      if ~~is_le dlo a then err "model comparison: lower bound beyond domain" else
      if ~~is_le b dhi then err "model comparison: upper bound beyond domain" else
      Sem p k
  | t_set _ q x => Sem (set_prm q p) x
  | t_var _ x => x
  | t_let _ _ x k => Sem p (k (Sem p x))
  end.
Definition Sem' p S (u: Term S): sval S := Sem p (u sval).

(** correctness of the above semantics
    the key lemma, [correct], is proved by induction on the parametricity relation *)
Definition cval S: sval S -> rval S -> Prop :=
  match S with
  | REAL => EP' contains
  | FUN  => EP' mcontains
  | BOOL => Eimpl
  | PRED => fun b p => Eimpl b (forall x, dlo <= x <= dhi -> p x)
  end.
Lemma correct S (u: term S) (v: term S): trel cval u v -> forall d, cval (Sem d u) (sem v).
Proof.
  induction 1; intro deg; cbn in *=>//.
  - eapply ep_map2; eauto. rel. 
  - eapply ep_map2; eauto. rel. 
  - eapply ep_map2; eauto. rel. 
  - constructor. rel. 
  - constructor. apply fromQR. 
  - constructor. rel. 
  - constructor. rel. 
  - constructor. rel.
  - eapply ep_map2; eauto. rel. 
  - eapply ep_map; eauto. rel. 
  - eapply ep_map; eauto. rel. 
  - eapply ep_map; eauto. rel. 
  - eapply ep_map; eauto. rel. 
  - eapply ep_bind=>[F Ff|]; eauto. 
    eapply ep_bind=>[X Xx|]; eauto.
    by apply mevalR.
  - eapply ep_bind=>[F Ff|]; eauto.  
    eapply ep_bind=>[A Aa|]; eauto.  
    eapply ep_bind=>[B Bb|]; eauto.  
    apply mintegrateR; rel. 
  - eapply ep_map2; eauto. intros. by apply: addR.
  - eapply ep_map2; eauto. intros. by apply: subR.
  - eapply ep_map2; eauto. intros. by apply: mulR.
  - eapply ep_bind=>[F Ff|]; eauto. 
    eapply ep_bind=>[G Gg|]; eauto.
    by apply mdivR.
  - eapply ep_bind=>[F Ff|]; eauto.
    by apply msqrtR.
  - apply midR.
  - apply mcosR.
  - apply msinR.
  - eapply ep_map; eauto. intros. by apply mcstR.
  - eapply ep_map; eauto. intros. by apply mtruncateR.
  - eapply ep_map2; eauto. intros ??. case is_leE=>//. auto.  
  - eapply ep_map2; eauto. intros ??. case is_geE=>//. auto. 
  - eapply ep_map2; eauto. intros ??. case is_ltE=>//. auto.
  - eapply ep_map2; eauto. intros ??. case is_neE=>//. auto.
  - by apply Eimpl_or.
  - by apply Eimpl_and.
  - eapply ep_bind=>[A HA|]; eauto.
    eapply ep_bind=>[B HB|]; eauto.
    case is_leE=>//=Ha. 
    case is_leE=>//=Hb.
    move: (IHtrel3 deg). apply Eimpl_impl=>E r ?. apply E. 
    specialize (Ha _ _ dloR HA).
    specialize (Hb _ _ HB dhiR).
    cbn in *. lra. 
  - eapply ep_bind=>[A HA|]; eauto.
    eapply ep_bind=>[B HB|]; eauto.
    eapply Eimpl_impl. 2: apply bisectE.
    move=>K z Hz. apply (K z). by eapply intervalE; eauto.
    move=>X. apply Eimpl_forall=>z. apply Eimpl_forall=>Hz. by auto.
  - eapply ep_bind=>[F Ff|]; eauto. 
    eapply ep_bind=>[G Gg|]; eauto.
    by apply mltE.
  - eapply ep_map2; eauto=>????. by apply mneE. 
  - apply Eimpl_or'.
    eapply Eimpl_impl. 2: apply IHtrel1. clear; auto. 
    eapply Eimpl_impl. 2: apply IHtrel2. clear; auto. 
  - eauto using Eimpl_and'.
  - eauto using Eimpl_impl. 
  - eapply ep_bind=>[A HA|]; eauto.
    eapply ep_bind=>[B HB|]; eauto.
    eapply Eimpl_impl. 2: apply bisectE.
    2: { move=>X. apply Eimpl_forall=>z. apply Eimpl_forall=>Hz. apply H2; eauto. } 
    move=>K z Hz t Ht. apply K=>//. by eapply intervalE; eauto.
  - auto. 
Qed.

(** correctness on parametric (closed) terms follows *)
Lemma Correct: forall p S (u: Term S), parametric u -> cval (Sem' p u) (sem' u).
Proof. intros p S u U. apply correct, U. Qed.

  
(** small corollary, useful to obtain a tactic in tactic.v *)
Lemma check p (b: Term BOOL):
  parametric b ->
  (let b := Sem' p b in
   match b with ret b => is_true b | err s => False end) ->
  sem' b.
Proof.
  move: (@Correct p BOOL)=>/= C B.
  case C=>//a. apply implE. 
Qed.

End s.
Arguments check {_ _ _ _} _ _ _ _.
Arguments Sem {_} _ _ [_] _.

End Static.


(** ** dynamic evaluation function *)
(** where we choose the basis according to integral bounds or quantifiers *)
Module Dynamic.
Section s.

Context {N: NBH} (MO: II -> II -> ModelOps) (M: forall D: Domain, Model (MO dlo dhi) dlo dhi).

(** interpretation of expressions using intervals / models / booleans *)
Definition sval S :=
  match S with
  | REAL => E II
  | FUN => (forall MO: ModelOps, E MM)
  | BOOL => E bool
  | PRED => (forall MO: ModelOps, E bool)
  end.
Fixpoint Sem (p: prms) S (t: @term sval S): sval S :=
  match t in term S return sval S with
  | e_add e f => e_map2 (@add _) (Sem p e) (Sem p f)
  | e_sub e f => e_map2 (@sub _) (Sem p e) (Sem p f)
  | e_mul e f => e_map2 (@mul _) (Sem p e) (Sem p f)
  | e_div e f => e_map2 (@div _) (Sem p e) (Sem p f)
  | e_sqrt e => e_map (@sqrt _) (Sem p e)
  | e_cos e => e_map (@cos _) (Sem p e)
  | e_sin e => e_map (@sin _) (Sem p e)
  | e_abs e => e_map (@abs _) (Sem p e)
  | e_fromQ q => ret (fromQ q)
  | e_fromZ z => ret (fromZ z)
  | e_pi => ret pi
  | e_zer => ret 0
  | e_one => ret 1
  | e_eval f x => err "evaluation not yet supported in dynamic mode"
      (* LET f ::= Sem p f IN *)
      (* LET x ::= Sem p x IN  *)
      (* meval f x *)
  | e_integrate f a b => 
      LET a ::= Sem p a IN 
      LET b ::= Sem p b IN 
      if ~~ is_lt a b then err "dynamic: integral does not yield a valid domain" else
      LET f ::= Sem p f (MO a b) IN 
      mintegrate f None None
  | f_add e f => fun MO => e_map2 (@add _) (Sem p e MO) (Sem p f MO)
  | f_sub e f => fun MO => e_map2 (@sub _) (Sem p e MO) (Sem p f MO)
  | f_mul e f => fun MO => e_map2 (@mul _) (Sem p e MO) (Sem p f MO)
  | f_div e f => fun MO => LET e ::= Sem p e MO IN LET f ::= Sem p f MO IN mdiv (p_deg p) (p_trunc p) e f
  | f_sqrt e => fun MO => LET e ::= Sem p e MO IN msqrt (p_deg p) (p_trunc p) e
  | f_id => fun MO => mid
  | f_cos => fun MO => mcos
  | f_sin => fun MO => msin
  | f_cst e => fun MO => e_map mcst (Sem p e)
  | f_trunc d e => fun MO => e_map (mtruncate d) (Sem p e MO)
  | b_le e f => e_map2 is_le (Sem p e) (Sem p f)
  | b_ge e f => e_map2 is_ge (Sem p e) (Sem p f) 
  | b_lt e f => e_map2 is_lt (Sem p e) (Sem p f)
  | b_ne e f => e_map2 is_ne (Sem p e) (Sem p f)
  | b_disj b c => Eor (Sem p b) (fun _ => Sem p c)
  | b_conj b c => Eand (Sem p b) (fun _ => Sem p c)
  | b_forall_models a b k => 
      LET a ::= Sem p a IN
      LET b ::= Sem p b IN
      bisect2 (p_depth p) (fun a b =>
                             if ~~ is_lt a b then err "invalid domain" else
                               Sem p k (MO a b)) a b
  | b_forall_bisect a b k =>
      LET a ::= Sem p a IN
      LET b ::= Sem p b IN
      bisect (p_depth p) (fun ab => Sem p (k (ret ab))) (interval a b)
  | c_lt f g =>
      fun M => 
      LET f ::= Sem p f M IN 
      LET g ::= Sem p g M IN
      mlt (p_deg p) f g
  | c_ne f g =>
      fun M => 
      LET f ::= Sem p f M IN 
      LET g ::= Sem p g M IN
      ret (mne (p_deg p) f g)
  | c_disj b c => fun M => Eor (Sem p b M) (fun _ => Sem p c M)
  | c_conj b c => fun M => Eand (Sem p b M) (fun _ => Sem p c M)
  | c_cst b => fun _ => Sem p b
  | c_forall_bisect a b k =>
      fun M =>
      LET a ::= Sem p a IN
      LET b ::= Sem p b IN
      bisect (p_depth p) (fun ab => Sem p (k (ret ab)) M) (interval a b)
  | t_set _ q x => Sem (set_prm q p) x
  | t_var _ x => x
  | t_let _ _ x k => Sem p (k (Sem p x))
  end.
Definition Sem' p S (u: Term S): sval S := Sem p (u sval).

(** correctness of the above semantics
    the key lemma, [correct], is proved by induction on the parametricity relation *)
Definition cval S: sval S -> rval S -> Prop :=
  match S with
  | REAL => EP' contains
  | FUN  => fun F f => forall MO a b (M: Model MO a b), EP' M (F MO) f
  | BOOL => Eimpl
  | PRED => fun P p => forall MO a b (M: Model MO a b), Eimpl (P MO) (forall x, a <= x <= b -> p x)
  end.
Lemma correct S (u: term S) (v: term S): trel cval u v -> forall p, cval (Sem p u) (sem v).
Proof.
  induction 1; intro ps; cbn -[RInt] in *;
    try (intros MO' a b M';
         try specialize (IHtrel  _ _ _ M');
         try (specialize (IHtrel1  _ _ _ M'); specialize (IHtrel2  _ _ _ M'))); trivial.
  - eapply ep_map2; eauto. rel. 
  - eapply ep_map2; eauto. rel. 
  - eapply ep_map2; eauto. rel. 
  - constructor. rel. 
  - constructor. apply fromQR. 
  - constructor. rel. 
  - constructor. rel. 
  - constructor. rel.
  - eapply ep_map2; eauto. rel. 
  - eapply ep_map; eauto. rel. 
  - eapply ep_map; eauto. rel. 
  - eapply ep_map; eauto. rel. 
  - eapply ep_map; eauto. rel. 
  - eapply ep_bind=>[A Aa|]; eauto.  
    eapply ep_bind=>[B Bb|]; eauto.  
    case_eq (is_lt A B)=>//=ab. 
    specialize (IHtrel1 ps _ _ _ (M (DfromI2 Aa Bb ab))).
    eapply ep_bind=>[F Ff|]; eauto.
    eapply mintegrateR; first apply Ff; by constructor. 
  - eapply ep_map2; eauto. intros. by apply: addR.
  - eapply ep_map2; eauto. intros. by apply: subR.
  - eapply ep_map2; eauto. intros. by apply: mulR.
  - eapply ep_bind=>[F Ff|]; eauto. 
    eapply ep_bind=>[G Gg|]; eauto.
    by apply mdivR.
  - eapply ep_bind=>[F Ff|]; eauto.
    by apply msqrtR.
  - apply midR.
  - apply mcosR.
  - apply msinR.
  - eapply ep_map; eauto. intros. by apply mcstR.
  - eapply ep_map; eauto. intros. by apply mtruncateR.
  - eapply ep_map2; eauto. intros ??. case is_leE=>//. auto.  
  - eapply ep_map2; eauto. intros ??. case is_geE=>//. auto. 
  - eapply ep_map2; eauto. intros ??. case is_ltE=>//. auto.
  - eapply ep_map2; eauto. intros ??. case is_neE=>//. auto.
  - by apply Eimpl_or.
  - by apply Eimpl_and.
  - eapply ep_bind=>[A Aa|]; eauto.
    eapply ep_bind=>[B Bb|]; eauto.
    eapply Eimpl_impl. 2: apply bisect2E.
    move=>K z Hz. cbn in *. eapply (K z); eauto.
    clear A Aa B Bb. 
    move=>A B. case_eq (is_lt A B)=>//=ab.
    apply Eimpl_forall=>z. 
    apply Eimpl_forall=>a. 
    apply Eimpl_forall=>b. 
    apply Eimpl_forall=>Aa. 
    apply Eimpl_forall=>Bb.
    move: z. apply <-(Eimpl_forall (A:=R)).
    apply IHtrel3. apply (M (DfromI2 Aa Bb ab)). 
  - eapply ep_bind=>[A HA|]; eauto.
    eapply ep_bind=>[B HB|]; eauto.
    eapply Eimpl_impl. 2: apply bisectE.
    move=>K z Hz. apply (K z). by eapply intervalE; eauto.
    move=>X. apply Eimpl_forall=>z. apply Eimpl_forall=>Hz. by auto.
  - eapply ep_bind=>[A Aa|]; eauto.  
    eapply ep_bind=>[B Bb|]; eauto.
    by apply mltE. 
  - eapply ep_bind=>[A Aa|]; eauto.  
    eapply ep_bind=>[B Bb|]; eauto.
    constructor. by apply mneE. 
  - apply Eimpl_or'.
    eapply Eimpl_impl. 2: apply IHtrel1; eassumption. clear; auto. 
    eapply Eimpl_impl. 2: apply IHtrel2; eassumption. clear; auto. 
  - eapply Eimpl_and'.
    apply IHtrel1; eassumption.
    apply IHtrel2; eassumption.
    auto. 
  - eauto using Eimpl_impl. 
  - eapply ep_bind=>[A HA|]; eauto.
    eapply ep_bind=>[B HB|]; eauto.
    eapply Eimpl_impl. 2: apply bisectE.
    2: { move=>X. apply Eimpl_forall=>z. apply Eimpl_forall=>Hz. apply H2; eauto. } 
    move=>K z Hz t Ht. apply K=>//. by eapply intervalE; eauto.
  - auto.
Qed.

(** correctness on parametric (closed) terms follows *)
Lemma Correct: forall p S (u: Term S), parametric u -> cval (Sem' p u) (sem' u).
Proof. intros p S u U. apply correct, U. Qed.

  
(** small corollary, useful to obtain a tactic in tactic.v *)
Lemma check p (b: Term BOOL):
  parametric b ->
  (let b := Sem' p b in
   match b with ret b => is_true b | err s => False end) ->
  sem' b.
Proof.
  move: (@Correct p BOOL)=>/= C B.
  case C=>//. apply implE.
Qed.

End s.
Arguments check {_ _} _ _ _.

End Dynamic.


(** ** notations for reified expressions *)
(** mostly used for tests in tests.v for now 
    sadly, trying to declare canonical structures of Ops0, Ops1, raises universe inconsistencies
 *)

Definition expr X := @term X REAL.
Definition fxpr X := @term X FUN.
Definition bxpr X := @term X BOOL.
Definition cxpr X := @term X PRED.

Declare Scope expr_scope.
Bind Scope expr_scope with expr.
Delimit Scope expr_scope with expr.
Definition e_add' X: expr X -> expr X -> expr X := e_add.
Definition e_sub' X: expr X -> expr X -> expr X := e_sub.
Definition e_mul' X: expr X -> expr X -> expr X := e_mul.
Definition e_div' X: expr X -> expr X -> expr X := e_div.
Infix "+" := e_add': expr_scope. 
Infix "-" := e_sub': expr_scope.
Infix "*" := e_mul': expr_scope.
Infix "/" := e_div': expr_scope.
Notation "0" := e_zer: expr_scope.
Notation "1" := e_one: expr_scope.
Definition fromQ' {X}: Q -> expr X := e_fromQ.
Definition fromZ' {X}: Z -> expr X := e_fromZ.
Definition sqrt' {X}: expr X -> expr X := e_sqrt.
Definition cos' {X}: expr X -> expr X := e_cos.
Definition sin' {X}: expr X -> expr X := e_sin.
Definition abs' {X}: expr X -> expr X:= e_abs.
Definition pi' {X}: expr X := e_pi.

Coercion cst' X: expr X -> fxpr X := f_cst.
Declare Scope fxpr_scope.
Bind Scope fxpr_scope with fxpr.
Delimit Scope fxpr_scope with fxpr.
Definition f_add' X: fxpr X -> fxpr X -> fxpr X := f_add.
Definition f_sub' X: fxpr X -> fxpr X -> fxpr X := f_sub.
Definition f_mul' X: fxpr X -> fxpr X -> fxpr X := f_mul.
Definition f_div' X: fxpr X -> fxpr X -> fxpr X := f_div.
Definition f_zer {X}: fxpr X := cst' 0. 
Definition f_one {X}: fxpr X := cst' 1. 
Infix "+" := f_add': fxpr_scope. 
Infix "-" := f_sub': fxpr_scope.
Infix "*" := f_mul': fxpr_scope.
Infix "/" := f_div': fxpr_scope.
Notation "0" := f_zer: fxpr_scope.
Notation "1" := f_one: fxpr_scope.

Definition integrate' X: fxpr X -> expr X -> expr X -> expr X := e_integrate.
Definition eval' X: fxpr X -> expr X -> expr X := e_eval.
Definition id' {X}: fxpr X := f_id.
Definition truncate' X: nat -> fxpr X -> fxpr X := f_trunc.
Definition fsqrt X: fxpr X -> fxpr X := f_sqrt.
Definition fcos X: fxpr X := f_cos.
Definition fsin X: fxpr X := f_sin.

Declare Scope bxpr_scope.
Bind Scope bxpr_scope with bxpr.
Delimit Scope bxpr_scope with bxpr.
Definition b_le' X: expr X -> expr X -> bxpr X := b_le.
Definition b_ge' X: expr X -> expr X -> bxpr X := b_ge.
Definition b_lt' X: expr X -> expr X -> bxpr X := b_lt.
Definition b_gt' X e f: bxpr X := b_lt' f e.
Definition b_conj' X: bxpr X -> bxpr X -> bxpr X := b_conj.
Definition b_disj' X: bxpr X -> bxpr X -> bxpr X := b_disj.
Infix "<=" := b_le': bxpr_scope. 
Infix "<" := b_lt': bxpr_scope. 
Infix ">=" := b_ge': bxpr_scope. 
Infix ">" := b_gt': bxpr_scope. 
Infix "/\" := b_conj': bxpr_scope. 
Infix "\/" := b_disj': bxpr_scope.

Declare Scope cxpr_scope.
Bind Scope cxpr_scope with cxpr.
Delimit Scope cxpr_scope with cxpr.
Definition c_lt' X: fxpr X -> fxpr X -> cxpr X := c_lt.
Definition c_ne' X: fxpr X -> fxpr X -> cxpr X := c_ne.
Definition c_conj' X: cxpr X -> cxpr X -> cxpr X := c_conj.
Definition c_disj' X: cxpr X -> cxpr X -> cxpr X := c_disj.
Coercion c_cst' X: bxpr X -> cxpr X := c_cst.
Infix "<" := c_lt': cxpr_scope. 
Infix "<>" := c_ne': cxpr_scope. 
Infix "/\" := c_conj': cxpr_scope. 
Infix "\/" := c_disj': cxpr_scope.

Definition b_forall_models' {X}: expr X -> expr X -> cxpr X -> bxpr X :=
  b_forall_models.
Definition b_forall_bisect' {X} (a b: expr X) (f: expr X -> bxpr X): bxpr X :=
  b_forall_bisect a b (fun x => f (t_var x)).
Definition c_forall_bisect' {X} (a b: expr X) (f: expr X -> cxpr X): cxpr X :=
  c_forall_bisect a b (fun x => f (t_var x)).
Arguments b_forall_bisect' {_} (_ _)%expr _%bxpr.
Arguments c_forall_bisect' {_} (_ _)%expr _%cxpr.

Notation "'let_e' x := e 'in' g" := (let' (e%expr: expr _) (fun (x: expr _) => (g%expr: expr _))) (at level 200, x binder, right associativity): expr_scope.
Notation "'let_e' x := e 'in' g" := (let' (e%expr: expr _) (fun (x: expr _) => (g%fxpr: fxpr _))) (at level 200, x binder, right associativity): fxpr_scope.
Notation "'let_e' x := e 'in' g" := (let' (e%expr: expr _) (fun (x: expr _) => (g%bxpr: bxpr _))) (at level 200, x binder, right associativity): bxpr_scope.
Notation "'let_e' x := e 'in' g" := (let' (e%expr: expr _) (fun (x: expr _) => (g%cxpr: cxpr _))) (at level 200, x binder, right associativity): cxpr_scope.
Notation "'let_f' x := e 'in' g" := (let' (e%fxpr: fxpr _) (fun (x: fxpr _) => (g%expr: expr _))) (at level 200, x binder, right associativity): expr_scope.
Notation "'let_f' x := e 'in' g" := (let' (e%fxpr: fxpr _) (fun (x: fxpr _) => (g%fxpr: fxpr _))) (at level 200, x binder, right associativity): fxpr_scope.
Notation "'let_f' x := e 'in' g" := (let' (e%fxpr: fxpr _) (fun (x: fxpr _) => (g%bxpr: bxpr _))) (at level 200, x binder, right associativity): bxpr_scope.
Notation "'let_f' x := e 'in' g" := (let' (e%fxpr: fxpr _) (fun (x: fxpr _) => (g%cxpr: cxpr _))) (at level 200, x binder, right associativity): cxpr_scope.

Notation EXPR t := ((fun X => (t%expr: expr X)): Term REAL).
Notation FXPR t := ((fun X => (t%fxpr: fxpr X)): Term FUN).
Notation BXPR t := ((fun X => (t%bxpr: bxpr X)): Term BOOL).
Notation CXPR t := ((fun X => (t%cxpr: cxpr X)): Term PRED).

(*
Check EXPR (1+e_pi).
Check EXPR (1+integrate' id' 0 1).
Check FXPR (id'/id').
Check EXPR (1+integrate' (id' / fsqrt id') 0 (fromQ' 3.3)).
Check EXPR (1+integrate' (id' / (fsqrt id' + fromZ' 3)) 0 (fromQ' 3.3)).
Check EXPR (1+integrate' (id' / (fsqrt id' + fromZ' 3)) 0 (fromQ' 3.3)).
Check EXPR (let_e x := 1+e_pi in x + x).
Check EXPR (let_e x := 1+e_pi in x + let_e y := x*x in sqrt' (y+y)).
Check FXPR (let_e x := 1+e_pi in id' + x).
Check FXPR (let_f f := 1-id' in id' * id').
Check BXPR (1 <= 0 \/ cos' pi' < 1 /\ cos' 0 >= 1).
Check BXPR (b_forall_bisect' 0 1 (fun c => integrate' (id'+c) 0 1 <= c+1/fromZ' 2) ).
Check BXPR (b_forall_models' 0 1 (id' < 0 /\ 1 <> fsqrt id')).
*) 
