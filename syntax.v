(** * Syntax for approximable expressions *)

Require Import String.
Require Import interfaces.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Universe Polymorphism.

(** sorts of expressions we know how to approximate 
    - [term ZER REAL]: real numbers (R)
    - [term ONE REAL]: functions on real numbers (R->R), seen as reals with one real parameter
    - [term ZER PROP]: (conjunctions/disjunctions) comparison of reals (Prop)
    - [term ONE PROP]: (conjunctions/disjunctions) comparison of functions, seen as propositions with one real parameter (R -> Prop)
 *)
Variant csort := REAL | PROP.
Variant dsort := ZER | ONE.

(** syntax for the expressions we know how to approximate 
    we use parameterised higher order abstract syntax (PHOAS) in order to have a let..in construct and be able to share subexpressions:
    [@term X S T] intuitively contains terms of sort [S,T] with variables in [X].
    Note that variables (from X) are independent from the potential parameter of a term
 *)
Inductive term {X: dsort -> csort -> Type}: dsort -> csort -> Type :=
(** real-valued expressions, with zero or one parameter *)
| t_add: forall {D}, term D REAL -> term D REAL -> term D REAL
| t_sub: forall {D}, term D REAL -> term D REAL -> term D REAL
| t_mul: forall {D}, term D REAL -> term D REAL -> term D REAL
| t_mul': forall {D}, nat -> term D REAL -> term D REAL -> term D REAL
| t_div: forall {D}, term D REAL -> term D REAL -> term D REAL
| t_sqrt: forall {D}, term D REAL -> term D REAL
| t_cos: forall {D}, term D REAL -> term D REAL
| t_sin: forall {D}, term D REAL -> term D REAL
| t_abs: forall {D}, term D REAL -> term D REAL
| t_fromZ: forall {D}, Z -> term D REAL
| t_fromQ: forall {D}, Q -> term D REAL
| t_zer: forall {D}, term D REAL
| t_one: forall {D}, term D REAL
| t_pi: forall {D}, term D REAL
(** identity function (the only construct giving access to the real parameter) *)
| t_id: term ONE REAL
(** function application (or substitution) *)
| t_app: term ONE REAL -> term ZER REAL -> term ZER REAL (* TOTHINK: also on PROP? *)
(** integration of a function *)
| t_integrate: term ONE REAL -> term ZER REAL -> term ZER REAL -> term ZER REAL
(** truncation request *)
| t_trunc: nat -> term ONE REAL -> term ONE REAL                                    
(** boolean-valued expressions, with zero or one parameter *)
| t_le: forall {D}, term D REAL -> term D REAL -> term D PROP
| t_ge: forall {D}, term D REAL -> term D REAL -> term D PROP
| t_lt: forall {D}, term D REAL -> term D REAL -> term D PROP
| t_ne: forall {D}, term D REAL -> term D REAL -> term D PROP
    (* don't need b_gt because Rgt unfolds to Rlt (while Rge does not unfold to Rle) *)
| t_disj: forall {D}, term D PROP -> term D PROP -> term D PROP
| t_conj: forall {D}, term D PROP -> term D PROP -> term D PROP
| t_true: forall {D}, term D PROP
| t_false: forall {D}, term D PROP
(** universal quantification over intervals, to be evaluated by model comparisons (and bisection) *)
| t_forall_models: term ZER REAL -> term ZER REAL -> term ONE PROP -> term ZER PROP
(** universal quantification over (thin) intervals, to be evaluated by bisection -- may have parameters *)
| t_forall_bisect: forall {D}, term D REAL -> term D REAL -> (X ZER REAL -> term D PROP) -> term D PROP
(** constant expressions not using their parameter (either boolean- or real- valued) *)
| t_cst: forall {C}, term ZER C -> term ONE C
(** setting evaluation parameters in a subexpression *)
| t_set {D C}: prm -> term D C -> term D C
(** let..in and variable, to enable sharing of some computations *)
| t_var: forall {D C}, X D C -> term D C
| t_let: forall {D C F E}, term D C -> (X D C -> term F E) -> term F E.

(** derived operations *)
Definition t_let' {X D C F E}: @term X D C -> (term D C -> term F E) -> term F E :=
  fun a k => t_let a (fun x => k (t_var x)). 
Definition t_forall_bisect' {X D}: term D REAL -> term D REAL -> (term ZER REAL -> term D PROP) -> @term X D PROP :=
  fun a b k => t_forall_bisect a b (fun x => k (t_var x)). 
Definition t_trunc' {X} d u: @term X ONE REAL := match d with None => u | Some d => t_trunc d u end.

(** closed terms: they act polymorphically in X *)
Definition Term D C := forall X, @term X D C.
(** (terms of sort D,C with a single variable of sort F,E would be represented by type 
    [forall X, X F E -> @term X D C]) *)


(** ** notations for reified expressions *)

(** structures to get access to the main notations from the library *)
Canonical Structure t_Ops0 X D: Ops0 := {|
  car := @term X D REAL;
  add := t_add;
  sub := t_sub;
  mul := t_mul;
  mul' := t_mul';
  zer := t_zer;
  one := t_one;
  mulZ z := t_mul (t_fromZ z);
  divZ z := t_div^~ (t_fromZ z);
|}.
Canonical Structure t_Ops1 X D: Ops1 := {|
  ops0 := t_Ops0 X D;
  fromZ := t_fromZ;
  div := t_div;
  sqrt := t_sqrt;
  cos := t_cos;
  sin := t_sin;
  abs := t_abs;
  pi := t_pi;
|}.

(** shorthands *)
Notation id' := t_id.
Notation integrate := t_integrate.
Notation forall_models := t_forall_models.
Notation forall_bisect := t_forall_bisect'.
Notation cst := t_cst.
Notation truncate := t_trunc.
Notation truncate' := t_trunc'.

(** additional notations, in a dedicated scope *)
Declare Scope term_scope.
Bind Scope term_scope with term.
Bind Scope term_scope with Term.
Delimit Scope term_scope with term.
Notation "'tlet' x := e 'in' g" := (t_let' e (fun x => g))
    (at level 200, x binder, right associativity): term_scope.
Notation "a > b" := (t_lt b a): term_scope. 
Infix "<=" := t_le: term_scope. 
Infix "<" := t_lt: term_scope. 
Infix ">=" := t_ge: term_scope. 
Infix "<>" := t_ne: term_scope. 
Infix "/\" := t_conj: term_scope. 
Infix "\/" := t_disj: term_scope.
Notation "x <= y <= z" := (tlet y' := y in x<=y' /\ y'<=z)%term: term_scope.
Notation "x <= y < z" := (tlet y' := y in x<=y' /\ y'<z)%term: term_scope.
Notation "x < y <= z" := (tlet y' := y in x<y' /\ y'<=z)%term: term_scope.
Notation "x < y < z" := (tlet y' := y in x<y' /\ y'<z)%term: term_scope.

(** notation to build a closed term (of type [Term _ _]) from a 'preterm' where the occurrences of X are not yet bound *)
Notation TERM t := ((fun X => (t%term: @term X _ _)): Term _ _).

(* tests for the above notations *)
(*
Check TERM (1+pi).
Check TERM (1+integrate id' 0 1).
Check TERM (id'/id').
Check TERM (sqrt (sqrt id')).
Check TERM (sqrt (sqrt (id'+sqrt id'))).
Check TERM (1+integrate (id' / sqrt id') 0 (fromQ 3.3)).
Check TERM (1+integrate (id' / (sqrt id' + fromZ 3)) 0 (fromQ 3.3)).
Check TERM (tlet x := 1+pi in x + x).
Check TERM (tlet x := 1+pi in x + tlet y := x*x in sqrt (y+y)).
Check TERM (tlet x := 1+pi in id' + x).
Check TERM (tlet f := 1-id' in id' * id').
Check TERM (tlet f := 1-id' in id' *[4] id').
Check TERM (1 <= 0 \/ cos pi < 1 /\ cos 0 >= 1).
Check TERM (1 <= cos pi < 1).
Check TERM (forall_bisect 0 1 (fun c => integrate (id'+cst c) 0 1 <= c+1/fromZ 2) ).
Check TERM (truncate 4 (cos id')).
*)


(** ** real number semantics of expressions  *)
Definition rval D C: Type :=
  match D,C with ZER,REAL => R | ONE,REAL => (R -> R) | ZER,PROP => Prop | ONE,PROP => R -> Prop end.
Fixpoint sem D C (t: @term rval D C): rval D C :=
  match t in term D C return rval D C with
  | t_add (ZER|ONE) e f => sem e + sem f
  | t_sub (ZER|ONE) e f => sem e - sem f
  | t_mul (ZER|ONE) e f => sem e * sem f
  | t_mul' (ZER|ONE) d e f => sem e *[d] sem f
  | t_div (ZER|ONE) e f => sem e / sem f
  | t_sqrt (ZER|ONE) e => sqrt (sem e)
  | t_cos (ZER|ONE) e => cos (sem e)
  | t_sin (ZER|ONE) e => sin (sem e)
  | t_abs (ZER|ONE) e => abs (sem e)
  | t_fromQ (ZER|ONE) q => fromQ q
  | t_fromZ (ZER|ONE) z => fromZ z
  | t_zer (ZER|ONE) => 0
  | t_one (ZER|ONE) => 1
  | t_pi (ZER|ONE) => pi
  | t_id => fun x => x
  | t_app f x => sem f (sem x)
  | t_integrate f a b => RInt (sem f) (sem a) (sem b)
  | t_cst (REAL|PROP) e => (fun _ => sem e)
  | t_trunc _ f => sem f
  | t_le ZER e f => sem e <= sem f
  | t_ge ZER e f => sem e >= sem f
  | t_lt ZER e f => sem e < sem f
  | t_ne ZER e f => sem e <> sem f
  | t_disj ZER b c => sem b \/ sem c
  | t_conj ZER b c => sem b /\ sem c
  | t_true ZER => True
  | t_false ZER => False
  | t_forall_bisect ZER a b k => forall x: R, sem a <= x <= sem b -> sem (k x)
  | t_forall_models a b k => forall x: R, sem a <= x <= sem b -> sem k x
  | t_le ONE e f => fun x => sem e x <= sem f x
  | t_ge ONE e f => fun x => sem e x >= sem f x
  | t_lt ONE e f => fun x => sem e x < sem f x
  | t_ne ONE e f => fun x => sem e x <> sem f x
  | t_disj ONE b c => fun x => sem b x \/ sem c x
  | t_conj ONE b c => fun x => sem b x /\ sem c x
  | t_true ONE => fun _ => True
  | t_false ONE => fun _ => False
  | t_forall_bisect ONE a b k => fun y => forall x: R, sem a y <= x <= sem b y -> sem (k x) y
  | t_set _ _ _ x => sem x
  | t_var _ _ x => x
  | t_let _ _ _ _ x k => sem (k (sem x))
  end.
Definition sem' D C (u: Term D C): rval D C := sem (u rval).


(** ** reification *)

(* TODO: 
   - detect constant sub-expressions (for [t_cst])
   - maximal sharing using let-ins? [need OCaml?]
   - reify user's let-ins?          [need OCaml?]
*)
Arguments f_bin [_ _] _ _ _ _ /.
Arguments f_unr [_ _] _ _ _ /.
Lemma VAR: R. exact R0. Qed.
Ltac reduce e :=
  eval cbn beta iota delta
       [ROps0 ROps1 f_Ops0 f_Ops1 car ops0 zer one add sub mul mul' div sqrt cos sin abs pi f_bin f_unr fromZ fromQ]
  in e.

Ltac reify e :=
  lazymatch e with
  | sem' (fun X => ?e) => e
  | R0 => uconstr:(t_zer)
  | R1 => uconstr:(t_one)
  | Rplus ?e ?f => let e:=reify e in let f:=reify f in uconstr:(t_add e f)
  | Rminus ?e ?f => let e:=reify e in let f:=reify f in uconstr:(t_sub e f)
  | Rmult ?e ?f => let e:=reify e in let f:=reify f in uconstr:(t_mul e f)
  | Rmult' ?d ?e ?f => let e:=reify e in let f:=reify f in uconstr:(t_mul' d e f)
  | Rdiv ?e ?f => let e:=reify e in let f:=reify f in uconstr:(t_div e f)
  | R_sqrt.sqrt ?e => let e:=reify e in uconstr:(t_sqrt e)
  | Rtrigo_def.cos ?e => let e:=reify e in uconstr:(t_cos e)
  | Rtrigo_def.sin ?e => let e:=reify e in uconstr:(t_sin e)
  | Rabs ?e => let e:=reify e in uconstr:(t_abs e)
  | Q2R ?q => uconstr:(t_fromQ q)
  | IZR ?z => uconstr:(t_fromZ z)
  | Rtrigo1.PI => uconstr:(t_pi)
  | RInt ?f ?a ?b =>
    let a:=reify a in
    let b:=reify b in
    let fVAR:=reduce (f VAR) in
    let f:=reify fVAR in
    uconstr:(t_integrate f a b)
  | Rtruncate ?d ?e => let e:=reify e in uconstr:(t_trunc d e)
  | VAR => uconstr:(t_id)
  | ?e <= ?f <= ?g =>
    let e:=reify e in let f:=reify f in let g:=reify g in
    uconstr:((e<=f<=g)%term)
  | ?e <= ?f < ?g =>
    let e:=reify e in let f:=reify f in let g:=reify g in
    uconstr:((e<=f<g)%term)
  | ?e < ?f <= ?g =>
    let e:=reify e in let f:=reify f in let g:=reify g in
    uconstr:((e<f<=g)%term)
  | ?e < ?f <= ?g =>
    let e:=reify e in let f:=reify f in let g:=reify g in
    uconstr:((e<f<g)%term)
  | Rle ?e ?f => let e:=reify e in let f:=reify f in uconstr:(t_le e f)
  | Rge ?e ?f => let e:=reify e in let f:=reify f in uconstr:(t_ge e f)
  | Rlt ?e ?f => let e:=reify e in let f:=reify f in uconstr:(t_lt e f)
  | Rgt ?f ?e => let e:=reify e in let f:=reify f in uconstr:(t_lt e f)
  | ?e <> ?f => let e:=reify e in let f:=reify f in uconstr:(t_ne e f)
  | ?b /\ ?c => let b:=reify b in let c:=reify c in uconstr:(t_conj b c)
  | ?b \/ ?c => let b:=reify b in let c:=reify c in uconstr:(t_disj b c)
  | True => uconstr:(t_true)
  | False => uconstr:(t_false)
  | forall x, ?a <= x <= ?b -> @?p x =>
    let a:=reify a in
    let b:=reify b in
    let pVAR:=reduce (p VAR) in
    let p:=reify pVAR in
    uconstr:(t_forall_models a b p)
  | set ?p ?e => let e:=reify e in uconstr:(t_set p e)
  (* | ?e => let e:=reify e in uconstr:(t_cst e) *)
  | ?e => fail "unrecognised expression:" e
  end.
Ltac reify_real e :=
  let e := reduce e in
  let e := reify e in
  constr:((fun X => e): Term ZER REAL).
Ltac reify_fun e :=
  let e := reduce (e VAR) in
  let e := reify e in
  constr:((fun X => e): Term ONE REAL).
Ltac reify_prop e :=
  let e := reduce e in
  let e := reify e in
  constr:((fun X => e): Term ZER PROP).

(* tests for the above reification tatics *)
(*
Ltac test r c := let e := r c in unify c (sem' e); pose e.
Goal True.
  test reify_real (Rplus R0 R1).
  test reify_real (42).
  test reify_real (4.2).
  test reify_real (0+1: R).
  test reify_real (RInt (fun z => z) R0 R1).
  test reify_real (RInt (fun z => R0) R0 R1).
  test reify_real (RInt (fun z => R0+z) R0 R1).
  test reify_real (RInt (fun z => R0+z) R0 R1).
  test reify_real (RInt sqrt R0 R1).
  test reify_real (RInt (sqrt + sqrt) R0 R1).
  test reify_real (RInt (sqrt *[4] sqrt) R0 R1).
  test reify_real (Rtrigo1.PI *[4] Rtrigo1.PI).
  test reify_real (RInt (fun x => sqrt x *[4] sqrt x) R0 R1).
  test reify_real (RInt (fun x => sqrt x *[4] (set (degree 5) (sqrt x))) R0 R1).
  test reify_real (RInt (fun x => sqrt x *[4] (Rtruncate 5 (sqrt x))) R0 R1).
  test reify_real (RInt (fun z => R0+z+cos (1/fromZ 2)) R0 R1).
  test reify_fun  (fun x: R => x * sqrt x).
  test reify_prop (1/2 <= 3 <= 1/2). (* DAGGER: double check *)
  test reify_prop (4 <= 5 <= 6).
  test reify_prop (4 < 5 /\ 3 <= RInt id 3.3 4.4 <= 18.9).
  test reify_prop (4 >= 5). 
  test reify_prop (forall x, 4 <= x <= 5 -> x*x < sqrt x).
  test reify_prop (set (degree 3) (1/2 <= 3) /\ set (depth 4) (0 <= 1/2)).
  test reify_prop (forall x, 2<=x<=cos 2 -> 1/x <> sqrt x). 
  Fail test reify_prop (forall x, 2<=x<=cos x -> 1/x <> sqrt x). 
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
Inductive trel X Y (R: forall D C, X D C -> Y D C -> Prop): forall D C, @term X D C -> @term Y D C -> Prop :=
| t_addR: forall D x y, trel R x y -> forall x' y', trel R x' y' -> trel R (D:=D) (t_add x x') (t_add y y')
| t_subR: forall D x y, trel R x y -> forall x' y', trel R x' y' -> trel R (D:=D) (t_sub x x') (t_sub y y')
| t_mulR: forall D x y, trel R x y -> forall x' y', trel R x' y' -> trel R (D:=D) (t_mul x x') (t_mul y y')
| t_mul'R: forall D d x y, trel R x y -> forall x' y', trel R x' y' -> trel R (D:=D) (t_mul' d x x') (t_mul' d y y')
| t_divR: forall D x y, trel R x y -> forall x' y', trel R x' y' -> trel R (D:=D) (t_div x x') (t_div y y')
| t_sqrtR: forall D x y, trel R x y -> trel R (D:=D) (t_sqrt x) (t_sqrt y)
| t_cosR: forall D x y, trel R x y -> trel R (D:=D) (t_cos x) (t_cos y)
| t_sinR: forall D x y, trel R x y -> trel R (D:=D) (t_sin x) (t_sin y)
| t_absR: forall D x y, trel R x y -> trel R (D:=D) (t_abs x) (t_abs y)
| t_fromZR: forall D z, trel R (D:=D) (t_fromZ z) (t_fromZ z)
| t_fromQR: forall D q, trel R (D:=D) (t_fromQ q) (t_fromQ q)
| t_zerR: forall D, trel R (D:=D) t_zer t_zer
| t_oneR: forall D, trel R (D:=D) t_one t_one
| t_piR: forall D, trel R (D:=D) t_pi t_pi
| t_idR: trel R t_id t_id
| t_appR: forall x y, trel R x y -> forall x' y', trel R x' y' -> trel R (t_app x x') (t_app y y')
| t_integrateR: forall f g, trel R f g -> forall x y, trel R x y -> forall x' y', trel R x' y' -> trel R (t_integrate f x x') (t_integrate g y y')
| t_cstR: forall C x y, trel R x y -> trel R (C:=C) (t_cst x) (t_cst y)
| t_truncR: forall d x y, trel R x y -> trel R (t_trunc d x) (t_trunc d y)
| t_leR: forall D x y, trel R x y -> forall x' y', trel R x' y' -> trel R (D:=D) (t_le x x') (t_le y y')
| t_geR: forall D x y, trel R x y -> forall x' y', trel R x' y' -> trel R (D:=D) (t_ge x x') (t_ge y y')
| t_ltR: forall D x y, trel R x y -> forall x' y', trel R x' y' -> trel R (D:=D) (t_lt x x') (t_lt y y')
| t_neR: forall D x y, trel R x y -> forall x' y', trel R x' y' -> trel R (D:=D) (t_ne x x') (t_ne y y')
| t_disjR: forall D x y, trel R x y -> forall x' y', trel R x' y' -> trel R (D:=D) (t_disj x x') (t_disj y y')
| t_conjR: forall D x y, trel R x y -> forall x' y', trel R x' y' -> trel R (D:=D) (t_conj x x') (t_conj y y')
| t_trueR: forall D, trel R (D:=D) t_true t_true
| t_falseR: forall D, trel R (D:=D) t_false t_false
| t_forall_modelsR: forall x y, trel R x y -> forall x' y', trel R x' y' -> forall h k, trel R h k -> 
                           trel R (t_forall_models x x' h) (t_forall_models y y' k)
| t_forall_bisectR: forall D x y, trel R x y -> forall x' y', trel R x' y' -> 
                    forall h k, (forall a b, R ZER REAL a b -> trel R (h a) (k b)) -> 
                           trel R (D:=D) (t_forall_bisect x x' h) (t_forall_bisect y y' k)
| t_setR: forall p D C x y, trel R x y -> trel R (@t_set _ D C p x) (@t_set _ D C p y)
| t_varR: forall D C x y, R D C x y -> trel R (t_var x) (t_var y)
| t_letR: forall D C F E x y h k, trel R x y -> (forall a b, R D C a b -> trel R (h a) (k b)) -> trel R (t_let x h) (@t_let _ _ _ F E y k).

(** all (closed) terms are parametric in the following sense, 
    but this cannot be proved once and for all. Given a concrete closed term, it is however trivial to prove its parametricity.
    once a closed term has been proved parametric, one can prove facts by induction on this term
    (see lemmas [Static.correct] and [Dynamic.correct] below) *)
Definition parametric D C (u: Term D C) :=
  forall X Y (R: forall D C, X D C -> Y D C -> Prop), trel R (u X) (u Y).
Ltac prove_parametric := repeat (constructor; auto).  
  

(** testing whether a term is the identity *)
Definition is_id X D C (t: @term X D C) :=
  match t with t_id => true | _ => false end.
Definition often_id X D C: @term X D C -> @term X D C :=
  match D,C with ONE,REAL => fun _ => t_id | _,_ => id end.
Lemma is_idE' X D C (t: @term X D C): impl (is_id t) (t=often_id t).
Proof. case: t=>//=. by constructor. Qed.
Lemma is_idE X (t: @term X ONE REAL): impl (is_id t) (t=t_id).
Proof. apply is_idE'. Qed.
Lemma is_idR X Y R D C s t: @trel X Y R D C s t -> is_id s = is_id t.
Proof. by case. Qed.

(** ** static evaluation function *)
(** where we fix a basis once and for all  *)
Module Static.
Section s.

Context {N: NBH} (MO: ModelOps) (Do: Domain) (M: Model MO dlo dhi). 

(** interpretation of expressions using intervals / models / booleans *)
Definition sval D C :=
  match C, D with
  | REAL,ZER => E II
  | REAL,ONE => E MM
  | PROP,_ => E bool
  end.
Fixpoint Sem (p: prms) D C (t: @term sval D C): sval D C :=
  match t in term D C return sval D C with
  | t_add (ZER|ONE) e f => e_map2 add (Sem p e) (Sem p f)
  | t_sub (ZER|ONE) e f => e_map2 sub (Sem p e) (Sem p f)
  | t_mul (ZER|ONE) e f => e_map2 mul (Sem p e) (Sem p f)
  | t_mul' (ZER|ONE) d e f => e_map2 (mul' d) (Sem p e) (Sem p f)
  | t_zer (ZER|ONE) => ret 0
  | t_one (ZER|ONE) => ret 1
  | t_div ZER e f => e_map2 div (Sem p e) (Sem p f)
  | t_sqrt ZER e => e_map sqrt (Sem p e)
  | t_cos ZER e => e_map cos (Sem p e)
  | t_sin ZER e => e_map sin (Sem p e)
  | t_abs ZER e => e_map abs (Sem p e)
  | t_fromQ ZER z => ret (fromQ z)
  | t_fromZ ZER z => ret (fromZ z)
  | t_pi ZER => ret pi
  | t_div ONE e f => LET e ::= Sem p e IN LET f ::= Sem p f IN mdiv (p_deg p) (p_trunc p) e f
  | t_sqrt ONE e => LET e ::= Sem p e IN msqrt (p_deg p) (p_trunc p) e
  | t_cos ONE e => if is_id e then mcos else err "cosine cannot be composed in models"
  | t_sin ONE e => if is_id e then msin else err "sine cannot be composed in models"
  | t_abs ONE e => err "absolute value not supported in models"
  | t_fromQ ONE q => ret (mcst (fromQ q))
  | t_fromZ ONE z => ret (mcst (fromZ z))
  | t_pi ONE => ret (mcst pi)
  | t_id => mid
  | t_app f x => 
      LET f ::= Sem p f IN
      LET x ::= Sem p x IN 
      meval f x
  | t_integrate f a b => 
      LET f ::= Sem p f IN 
      LET a ::= Sem p a IN 
      LET b ::= Sem p b IN 
      mintegrate f (Some a) (Some b)
  | t_cst REAL e => e_map mcst (Sem p e)
  | t_cst PROP e => Sem p e
  | t_trunc d e => e_map (mtruncate d) (Sem p e)
  | t_le ZER e f => e_map2 is_le (Sem p e) (Sem p f)
  | t_ge ZER e f => e_map2 is_ge (Sem p e) (Sem p f)
  | t_lt ZER e f => e_map2 is_lt (Sem p e) (Sem p f)
  | t_ne ZER e f => e_map2 is_ne (Sem p e) (Sem p f)
  | t_disj _ b c => Eor (Sem p b) (fun _ => Sem p c)
  | t_conj _ b c => Eand (Sem p b) (fun _ => Sem p c)
  | t_true _ => ret true
  | t_false _ => ret false
  | t_le ONE f g =>
      LET f ::= Sem p f IN LET g ::= Sem p g IN mle (p_deg p) f g
  | t_ge ONE f g =>
      LET f ::= Sem p f IN LET g ::= Sem p g IN mge (p_deg p) f g
  | t_lt ONE f g =>
      LET f ::= Sem p f IN LET g ::= Sem p g IN mlt (p_deg p) f g
  | t_ne ONE f g => e_map2 (mne (p_deg p)) (Sem p f) (Sem p g)
  | t_forall_bisect ZER a b k => 
      LET a ::= Sem p a IN
      LET b ::= Sem p b IN
      bisect (p_depth p) (fun x => Sem p (k (ret x))) (interval a b)
  | t_forall_bisect ONE a b k => 
      LET a ::= Sem p a IN
      LET b ::= Sem p b IN
      bisect (p_depth p) (fun x => Sem p (k (ret x))) (interval (mrange a) (mrange b))
  | t_forall_models a b k => 
      LET a ::= Sem p a IN
      LET b ::= Sem p b IN
      if ~~is_le dlo a then err "model comparison: lower bound beyond domain" else
      if ~~is_le b dhi then err "model comparison: upper bound beyond domain" else
      Sem p k
  | t_set _ _ q x => Sem (set_prm q p) x
  | t_var _ _ x => x
  | t_let _ _ _ _ x k => Sem p (k (Sem p x))
  end.
Definition Sem' p D C (u: Term D C): sval D C := Sem p (u sval).

(** correctness of the above semantics
    the key lemma, [correct], is proved by induction on the parametricity relation *)
Definition cval D C: sval D C -> rval D C -> Prop :=
  match D,C with
  | ZER,REAL => EP' contains
  | ONE,REAL  => EP' mcontains
  | ZER,PROP => Eimpl
  | ONE,PROP => fun b p => Eimpl b (forall x, dlo <= x <= dhi -> p x)
  end.
Lemma correct D C (u: term D C) (v: term D C): trel cval u v -> forall d, cval (Sem d u) (sem v).
Proof.
  induction 1=>ps/=; 
                 lazymatch goal with
                 | |- context [match ?x with _ => _ end] => destruct x
                 | _ => idtac
                 end;
    cbn in *=>//; try ((eapply ep_map || eapply ep_map2 || constructor); eauto; rel).
  - eapply ep_map2; eauto. unfold Rmult'; rel. 
  - eapply ep_bind=>[F Ff|]; eauto. 
    eapply ep_bind=>[G Gg|]; eauto.
    by apply mdivR.
  - eapply ep_bind=>[F Ff|]; eauto.
    by apply msqrtR.
  - move: (is_idR H). case is_idE=>//. case is_idE=>//-> _ _. apply mcosR. 
  - move: (is_idR H). case is_idE=>//. case is_idE=>//-> _ _. apply msinR. 
  - constructor. apply: mcstR; rel.
  - constructor. rewrite /f_unr/f_cst/=. apply: mcstR; rel.
  - constructor. apply: mcstR; rel.
  - apply midR.
  - eapply ep_bind=>[F Ff|]; eauto. 
    eapply ep_bind=>[X Xx|]; eauto.
    by apply mevalR.
  - eapply ep_bind=>[F Ff|]; eauto.  
    eapply ep_bind=>[A Aa|]; eauto.  
    eapply ep_bind=>[B Bb|]; eauto.  
    apply mintegrateR; rel. 
  - case IHtrel=>//b Hb. constructor. case Hb=>//. by constructor. 
  - eapply ep_map; eauto=>*. by apply mtruncateR.
  - eapply ep_map2; eauto=>??. case is_leE=>//. auto.  
  - eapply ep_bind=>[F Ff|]; eauto. 
    eapply ep_bind=>[X Xx|]; eauto.
    by apply mleE.
  - eapply ep_map2; eauto=>??. case is_geE=>//. auto.  
  - eapply ep_bind=>[F Ff|]; eauto. 
    eapply ep_bind=>[X Xx|]; eauto.
    by apply mgeE.
  - eapply ep_map2; eauto=>??. case is_ltE=>//. auto.  
  - eapply ep_bind=>[F Ff|]; eauto. 
    eapply ep_bind=>[X Xx|]; eauto.
    by apply mltE.
  - eapply ep_map2; eauto=>??. case is_neE=>//. auto.  
  - eapply ep_bind=>[F Ff|]; eauto. 
    eapply ep_bind=>[X Xx|]; eauto.
    constructor. by apply mneE.
  - apply Eimpl_or'.
    eapply Eimpl_impl. 2: apply IHtrel1. clear; auto. 
    eapply Eimpl_impl. 2: apply IHtrel2. clear; auto.     
  - apply Eimpl_or'.
    eapply Eimpl_impl. 2: apply IHtrel1. clear; auto. 
    eapply Eimpl_impl. 2: apply IHtrel2. clear; auto. 
  - eauto using Eimpl_and'.
  - eauto using Eimpl_and'.
  - eapply ep_bind=>[A HA|]; eauto.
    eapply ep_bind=>[B HB|]; eauto.
    case is_leE=>//=Ha. 
    case is_leE=>//=Hb.
    move: (IHtrel3 ps). apply Eimpl_impl=>E r ?. apply E. 
    specialize (Ha _ _ dloR HA).
    specialize (Hb _ _ HB dhiR).
    cbn in *. lra. 
  - eapply ep_bind=>[A HA|]; eauto.
    eapply ep_bind=>[B HB|]; eauto.
    eapply Eimpl_impl. 2: apply bisectE.
    2: { move=>X. apply Eimpl_forall=>z. apply Eimpl_forall=>Hz. apply H2; eauto. } 
    move=>K z Hz. apply K=>//. by eapply intervalE; eauto.
  - eapply ep_bind=>[A HA|]; eauto.
    eapply ep_bind=>[B HB|]; eauto.
    eapply Eimpl_impl. 2: apply bisectE.
    2: { move=>X. apply Eimpl_forall=>z. apply Eimpl_forall=>Hz. apply H2; eauto. } 
    move=>K z Hz t Ht. apply K=>//.
    by eapply intervalE; eauto; apply mrangeR.
  - auto. 
Qed.

(** correctness on parametric (closed) terms follows *)
Lemma Correct: forall p D C (u: Term D C), parametric u -> cval (Sem' p u) (sem' u).
Proof. move=>*. by apply correct. Qed.
  
(** small corollary, useful to obtain a tactic in tactic.v *)
Lemma check p (b: Term ZER PROP):
  parametric b ->
  (let b := Sem' p b in
   match b with ret b => is_true b | err s => False end) ->
  sem' b.
Proof.
  move: (@Correct p ZER PROP)=>/= C B.
  case C=>//a. apply implE. 
Qed.

End s.
Arguments check {_ _ _ _} _ _ _ _.
Arguments Sem {_} _ _ [_ _] _.

End Static.


(** ** dynamic evaluation function *)
(** where we choose the basis according to integral bounds or quantifiers *)
Module Dynamic.
Section s.

Context {N: NBH} (MO: II -> II -> ModelOps) (M: forall D: Domain, Model (MO dlo dhi) dlo dhi).

(** interpretation of expressions using intervals / models / booleans *)
Definition sval D C :=
  match D,C with
  | ZER,REAL => E II
  | ONE,REAL => (forall MO: ModelOps, E MM)
  | ZER,PROP => E bool
  | ONE,PROP => (forall MO: ModelOps, E bool)
  end.
Fixpoint Sem (p: prms) D C (t: @term sval D C): sval D C :=
  match t in term D C return sval D C with
  | t_add ZER e f => e_map2 add (Sem p e) (Sem p f)
  | t_sub ZER e f => e_map2 sub (Sem p e) (Sem p f)
  | t_mul ZER e f => e_map2 mul (Sem p e) (Sem p f)
  | t_mul' ZER d e f => e_map2 (mul' d) (Sem p e) (Sem p f)
  | t_zer ZER => ret 0
  | t_one ZER => ret 1
  | t_div ZER e f => e_map2 div (Sem p e) (Sem p f)
  | t_sqrt ZER e => e_map sqrt (Sem p e)
  | t_cos ZER e => e_map cos (Sem p e)
  | t_sin ZER e => e_map sin (Sem p e)
  | t_abs ZER e => e_map abs (Sem p e)
  | t_fromQ ZER z => ret (fromQ z)
  | t_fromZ ZER z => ret (fromZ z)
  | t_pi ZER => ret pi
  | t_add ONE e f => fun MO => e_map2 add (Sem p e MO) (Sem p f MO)
  | t_sub ONE e f => fun MO => e_map2 sub (Sem p e MO) (Sem p f MO)
  | t_mul ONE e f => fun MO => e_map2 mul (Sem p e MO) (Sem p f MO)
  | t_mul' ONE d e f => fun MO => e_map2 (mul' d) (Sem p e MO) (Sem p f MO)
  | t_zer ONE => fun MO => ret 0
  | t_one ONE => fun MO => ret 1
  | t_div ONE e f => fun MO => LET e ::= Sem p e MO IN LET f ::= Sem p f MO IN mdiv (p_deg p) (p_trunc p) e f
  | t_sqrt ONE e => fun MO => LET e ::= Sem p e MO IN msqrt (p_deg p) (p_trunc p) e
  | t_cos ONE e => fun MO => if is_id e then mcos else err "cosine cannot be composed in models"
  | t_sin ONE e => fun MO => if is_id e then msin else err "sine cannot be composed in models"
  | t_abs ONE e => fun MO => err "absolute value not supported in models"
  | t_fromQ ONE q => fun MO => ret (mcst (fromQ q))
  | t_fromZ ONE z => fun MO => ret (mcst (fromZ z))
  | t_pi ONE => fun MO => ret (mcst pi)
  | t_id => fun MO => mid
  | t_app f x => err "application not yet supported in dynamic mode"
  | t_integrate f a b => 
      LET a ::= Sem p a IN 
      LET b ::= Sem p b IN 
      if ~~ is_lt a b then err "dynamic: integral does not yield a valid domain" else
      LET f ::= Sem p f (MO a b) IN 
      mintegrate f None None
  | t_cst REAL e => fun MO => e_map mcst (Sem p e)
  | t_cst PROP e => fun MO => Sem p e
  | t_trunc d e => fun MO => e_map (mtruncate d) (Sem p e MO)
  | t_le ZER e f => e_map2 is_le (Sem p e) (Sem p f)
  | t_ge ZER e f => e_map2 is_ge (Sem p e) (Sem p f)
  | t_lt ZER e f => e_map2 is_lt (Sem p e) (Sem p f)
  | t_ne ZER e f => e_map2 is_ne (Sem p e) (Sem p f)
  | t_disj ZER b c => Eor (Sem p b) (fun _ => Sem p c)
  | t_conj ZER b c => Eand (Sem p b) (fun _ => Sem p c)
  | t_true ZER => ret true
  | t_false ZER => ret false
  | t_disj ONE b c => fun MO => Eor (Sem p b MO) (fun _ => Sem p c MO)
  | t_conj ONE b c => fun MO => Eand (Sem p b MO) (fun _ => Sem p c MO)
  | t_true ONE => fun MO => ret true
  | t_false ONE => fun MO => ret false
  | t_lt ONE f g =>
      fun MO => LET f ::= Sem p f MO IN LET g ::= Sem p g MO IN mlt (p_deg p) f g
  | t_le ONE f g =>
      fun MO => LET f ::= Sem p f MO IN LET g ::= Sem p g MO IN mle (p_deg p) f g
  | t_ge ONE f g =>
      fun MO => LET f ::= Sem p f MO IN LET g ::= Sem p g MO IN mge (p_deg p) f g
  | t_ne ONE f g => 
      fun MO => e_map2 (mne (p_deg p)) (Sem p f MO) (Sem p g MO)
  | t_forall_bisect ZER a b k => 
      LET a ::= Sem p a IN
      LET b ::= Sem p b IN
      bisect (p_depth p) (fun x => Sem p (k (ret x))) (interval a b)
  | t_forall_bisect ONE a b k => 
      fun MO =>
      LET a ::= Sem p a MO IN
      LET b ::= Sem p b MO IN
      bisect (p_depth p) (fun x => Sem p (k (ret x)) MO) (interval (mrange a) (mrange b))
  | t_forall_models a b k => 
      LET a ::= Sem p a IN
      LET b ::= Sem p b IN
      bisect2 (p_depth p) (fun a b =>
                             if ~~ is_lt a b then err "invalid domain" else
                               Sem p k (MO a b)) a b
  | t_set _ _ q x => Sem (set_prm q p) x
  | t_var _ _ x => x
  | t_let _ _ _ _ x k => Sem p (k (Sem p x))
  end.
Definition Sem' p D C (u: Term D C): sval D C := Sem p (u sval).

(** correctness of the above semantics
    the key lemma, [correct], is proved by induction on the parametricity relation *)
Definition cval D C: sval D C -> rval D C -> Prop :=
  match D,C with
  | ZER,REAL => EP' contains
  | ONE,REAL => fun F f => forall MO a b (M: Model MO a b), EP' M (F MO) f
  | ZER,PROP => Eimpl
  | ONE,PROP => fun P p => forall MO a b (M: Model MO a b), Eimpl (P MO) (forall x, a <= x <= b -> p x)
  end.
Lemma correct D C (u: term D C) (v: term D C): trel cval u v -> forall p, cval (Sem p u) (sem v).

Proof.
  induction 1=>ps/=; 
                 lazymatch goal with
                 | |- context [match ?x with _ => _ end] => destruct x
                 | _ => idtac
                 end;
    cbn -[RInt] in *=>//; try intros MO' a b M'; 
    try ((eapply ep_map || eapply ep_map2 || constructor); eauto; rel).
  - eapply ep_map2; eauto. unfold Rmult'; rel. 
  - eapply ep_bind=>[F Ff|]; eauto. 
    eapply ep_bind=>[G Gg|]; eauto.
    by apply mdivR.
  - eapply ep_bind=>[F Ff|]; eauto.
    by apply msqrtR.
  - move: (is_idR H). case is_idE=>//. case is_idE=>//-> _ _. apply mcosR. 
  - move: (is_idR H). case is_idE=>//. case is_idE=>//-> _ _. apply msinR. 
  - constructor. apply: mcstR; rel.
  - constructor. rewrite /f_unr/f_cst/=. apply: mcstR; rel.
  - constructor. apply: mcstR; rel.
  - apply midR.
  - eapply ep_bind=>[A Aa|]; eauto.  
    eapply ep_bind=>[B Bb|]; eauto.  
    case_eq (is_lt A B)=>//=ab. 
    specialize (IHtrel1 ps _ _ _ (M (DfromI2 Aa Bb ab))).
    eapply ep_bind=>[F Ff|]; eauto.
    eapply mintegrateR; first apply Ff; by constructor. 
  - case IHtrel=>//c Hc. constructor. case Hc=>//. by constructor. 
  - eapply ep_map; eauto=>*. by apply mtruncateR.
  - eapply ep_map2; eauto=>??. case is_leE=>//. auto.  
  - eapply ep_bind=>[F Ff|]; eauto. 
    eapply ep_bind=>[X Xx|]; eauto.
    by apply mleE.
  - eapply ep_map2; eauto=>??. case is_geE=>//. auto.  
  - eapply ep_bind=>[F Ff|]; eauto. 
    eapply ep_bind=>[X Xx|]; eauto.
    by apply mgeE.
  - eapply ep_map2; eauto=>??. case is_ltE=>//. auto.  
  - eapply ep_bind=>[F Ff|]; eauto. 
    eapply ep_bind=>[X Xx|]; eauto.
    by apply mltE.
  - eapply ep_map2; eauto=>??. case is_neE=>//. auto.  
  - eapply ep_bind=>[F Ff|]; eauto. 
    eapply ep_bind=>[X Xx|]; eauto.
    constructor. by apply mneE.
  - apply Eimpl_or'.
    eapply Eimpl_impl. 2: apply IHtrel1. clear; auto. 
    eapply Eimpl_impl. 2: apply IHtrel2. clear; auto.     
  - apply Eimpl_or'.
    eapply Eimpl_impl. 2: apply IHtrel1; eauto. clear; auto. 
    eapply Eimpl_impl. 2: apply IHtrel2; eauto. clear; auto. 
  - eapply Eimpl_and'.
    apply IHtrel1; eassumption.
    apply IHtrel2; eassumption.
    auto.     
  - eapply Eimpl_and'.
    apply IHtrel1; eassumption.
    apply IHtrel2; eassumption.
    auto.     
  - eapply ep_bind=>[A HA|]; eauto.
    eapply ep_bind=>[B HB|]; eauto.
    eapply Eimpl_impl. 2: apply bisect2E.
    move=>K z Hz. cbn in *. eapply (K z); eauto.
    clear A HA B HB. 
    move=>A B. case_eq (is_lt A B)=>//=ab.
    apply Eimpl_forall=>z. 
    apply Eimpl_forall=>a. 
    apply Eimpl_forall=>b. 
    apply Eimpl_forall=>HA. 
    apply Eimpl_forall=>HB.
    move: z. apply <-(Eimpl_forall (A:=R)).
    apply IHtrel3. apply (M (DfromI2 HA HB ab)). 
  - eapply ep_bind=>[A HA|]; eauto.
    eapply ep_bind=>[B HB|]; eauto.
    eapply Eimpl_impl. 2: apply bisectE.
    2: { move=>X. apply Eimpl_forall=>z. apply Eimpl_forall=>Hz. apply H2; eauto. } 
    move=>K z Hz. apply K=>//. by eapply intervalE; eauto.
  - eapply ep_bind=>[A HA|]; eauto.
    eapply ep_bind=>[B HB|]; eauto.
    eapply Eimpl_impl. 2: apply bisectE.
    2: { move=>X. apply Eimpl_forall=>z. apply Eimpl_forall=>Hz. apply H2; eauto. } 
    move=>K z Hz t Ht. apply K=>//.
    by eapply intervalE; eauto; apply mrangeR.
  - auto. 
Qed.

(** correctness on parametric (closed) terms follows *)
Lemma Correct: forall p D C (u: Term D C), parametric u -> cval (Sem' p u) (sem' u).
Proof. move=>*; by apply correct. Qed.
  
(** small corollary, useful to obtain a tactic in tactic.v *)
Lemma check p (b: Term ZER PROP):
  parametric b ->
  (let b := Sem' p b in
   match b with ret b => is_true b | err s => False end) ->
  sem' b.
Proof.
  move: (@Correct p ZER PROP)=>/= C B.
  case C=>//. apply implE.
Qed.

End s.
Arguments check {_ _} _ _ _.

End Dynamic.

(* checking universe constraints *)
(*
Check Dynamic.check _ _ (TERM (1<pi)).
 *)
