(** * Syntax for approximable expressions *)

Require Import String.
Require Import interfaces.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** sorts of expressions we know how to approximate 
    - real numbers
    - functions on closed real intervals
    - (conjunctions/disjunctions of combinations of) comparison of reals
 *)
Variant sort := REAL | FUN | BOOL.

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
| f_trunc: Z -> term FUN -> term FUN         (* the identity, simply truncates the model *)
(* boolean expressions *)
| b_le: term REAL -> term REAL -> term BOOL
| b_ge: term REAL -> term REAL -> term BOOL
| b_lt: term REAL -> term REAL -> term BOOL
| b_ne: term REAL -> term REAL -> term BOOL
    (* need b_ge and not b_gt because Rgt unfolds to Rlt while Rge does not unfold to Rle *)
| b_disj: term BOOL -> term BOOL -> term BOOL
| b_conj: term BOOL -> term BOOL -> term BOOL
    (* testing < or <> on a given domain (to be generalised) *)
| b_mlt: term REAL -> term REAL -> term FUN -> term FUN -> term BOOL
| b_mne: term REAL -> term REAL -> term FUN -> term FUN -> term BOOL
| b_impl: term BOOL -> term BOOL -> term BOOL
| b_forall: (X REAL -> term BOOL) -> term BOOL
(* setting the degree in a subexpression *)
| t_deg {S}: Z -> term S -> term S
(* let..in and variable *)
| t_var: forall {S}, X S -> term S
| t_let: forall {S T}, term S -> (X S -> term T) -> term T.
Definition let' {X S T}: @term X S -> (term S -> term T) -> term T :=
  fun a k => t_let a (fun x => k (t_var x)). 

(** closed terms: they act polymorphically in X *)
Definition Term S := forall X, @term X S.
(** (terms of sort T with a single variable of sort S would be represented by type 
    [forall X, X S -> @term X T]) *)


(** ** real number semantics of expressions  *)
Definition rval S: Type := match S with REAL => R | FUN => (R -> R) | BOOL => Prop end.
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
  | b_mlt a b f g => forall x, sem a <= x <= sem b -> sem f x < sem g x
  | b_mne a b f g => forall x, sem a <= x <= sem b -> sem f x <> sem g x
  | b_impl b c => sem b -> sem c
  | b_forall k => forall x: R, sem (k x)
  | t_deg _ _ x => sem x
  | t_var _ x => x
  | t_let _ _ x k => sem (k (sem x))
  end.
Definition sem' S (u: Term S): rval S := sem (u rval).



(** ** reification for the above syntax *)

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
  | at_degree ?d ?e => let e:=ereify e in uconstr:(t_deg d e)
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
  | Rplus ?e ?f => let e:=freify e in let f:=freify f in uconstr:(f_add e f)
  | Rminus ?e ?f => let e:=freify e in let f:=freify f in uconstr:(f_sub e f)
  | Rmult ?e ?f => let e:=freify e in let f:=freify f in uconstr:(f_mul e f)
  | Rmult' ?d ?e ?f => let e:=freify e in let f:=freify f in uconstr:(f_trunc d (f_mul e f))
  | Rtruncate ?d ?e => let e:=freify e in uconstr:(f_trunc d e)
  | Rdiv ?e ?f => let e:=freify e in let f:=freify f in uconstr:(f_div e f)
  | R_sqrt.sqrt ?e => let e:=freify e in uconstr:(f_sqrt e)
  | at_degree ?d ?e => let e:=freify e in uconstr:(t_deg d e)
  | Rtrigo_def.cos VAR => uconstr:(f_cos)
  | Rtrigo_def.sin VAR => uconstr:(f_sin)
  | VAR => uconstr:(f_id)
  | ?e => let e:=ereify e in uconstr:(f_cst e)
    end.
Ltac breify b :=
  lazymatch b with
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
  | at_degree ?d ?e => let e:=breify e in uconstr:(t_deg d e)
  | forall x, ?a <= x <= ?b -> @?f x < @?g x =>
    let a:=ereify a in
    let b:=ereify b in
    let fVAR:=reduce (f VAR) in
    let f:=freify fVAR in
    let gVAR:=reduce (g VAR) in
    let g:=freify gVAR in
    uconstr:(b_mlt a b f g)
  | forall x, ?a <= x <= ?b -> @?f x <> @?g x =>
    let a:=ereify a in
    let b:=ereify b in
    let fVAR:=reduce (f VAR) in
    let f:=freify fVAR in
    let gVAR:=reduce (g VAR) in
    let g:=freify gVAR in
    uconstr:(b_mne a b f g)
  | ?b -> ?c => let b:=breify b in let c:=breify c in uconstr:(b_impl b c)
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

(*
(* tests for the above reification tatics *)
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
  let e := reify_real constr:(RInt (fun x => sqrt x *[4] (at_degree 5 (sqrt x))) R0 R1) in pose e.
  let e := reify_real constr:(RInt (fun x => sqrt x *[4] (Rtruncate 5 (sqrt x))) R0 R1) in pose e.
  let e := reify_real constr:(RInt (fun z => R0+z+cos (1/fromZ 2)) R0 R1) in pose e.
  let f := reify_fun  constr:(fun x: R => x * sqrt x) in pose f.
  let b := reify_prop constr:(1/2 <= 3 <= 1/2) in pose b. (* DAGGER: double check *)
  let b := reify_prop constr:(4 <= 5 <= 6) in pose b.
  let b := reify_prop constr:(4 < 5 /\ 3 <= RInt id 3.3 4.4 <= 18.9) in pose b.
  let b := reify_prop constr:(4 >= 5) in pose b. 
  let b := reify_prop constr:(forall x, 4 <= x <= 5 -> x*x < sqrt x) in pose b.
  let b := reify_prop constr:(at_degree 3 (1/2 <= 3) /\ at_degree 4 (0 <= 1/2)) in pose b. (* DAGGER: double check *)
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
| rb_mlt: forall x y, trel R x y -> forall x' y', trel R x' y' ->
          forall f g, trel R f g -> forall h k, trel R h k -> trel R (b_mlt x x' f h) (b_mlt y y' g k)
| rb_mne: forall x y, trel R x y -> forall x' y', trel R x' y' ->
          forall f g, trel R f g -> forall h k, trel R h k -> trel R (b_mne x x' f h) (b_mne y y' g k)
| rb_impl: forall x y, trel R x y -> forall x' y', trel R x' y' -> trel R (b_impl x x') (b_impl y y')
| rb_forall: forall h k, (forall a b, R REAL a b -> trel R (h a) (k b)) -> trel R (b_forall h) (b_forall k)
| rt_deg: forall d S x y, trel R x y -> trel R (@t_deg _ S d x) (@t_deg _ S d y)
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

Context {N: NBH} (MO: ModelOps) lo hi (M: Model MO lo hi). 


(** interpretation of expressions using intervals / models / booleans *)
Definition sval S :=
  match S with
  | REAL => E II
  | FUN => E MM
  | BOOL => E bool
  end.
Fixpoint Sem d S (t: @term sval S): sval S :=
  match t in term S return sval S with
  | e_add e f => e_map2 (@add _) (Sem d e) (Sem d f)
  | e_sub e f => e_map2 (@sub _) (Sem d e) (Sem d f)
  | e_mul e f => e_map2 (@mul _) (Sem d e) (Sem d f)
  | e_div e f => e_map2 (@div _) (Sem d e) (Sem d f)
  | e_sqrt e => e_map (@sqrt _) (Sem d e)
  | e_cos e => e_map (@cos _) (Sem d e)
  | e_sin e => e_map (@sin _) (Sem d e)
  | e_abs e => e_map (@abs _) (Sem d e)
  | e_fromQ q => ret (fromQ q)
  | e_fromZ z => ret (fromZ z)
  | e_pi => ret pi
  | e_zer => ret 0
  | e_one => ret 1
  | e_eval f x => 
      LET f ::= Sem d f IN
      LET x ::= Sem d x IN 
      meval f x
  | e_integrate f a b => 
      LET f ::= Sem d f IN 
      LET a ::= Sem d a IN 
      LET b ::= Sem d b IN 
      mintegrate f (Some a) (Some b)
  | f_add e f => e_map2 (@add _) (Sem d e) (Sem d f)
  | f_sub e f => e_map2 (@sub _) (Sem d e) (Sem d f)
  | f_mul e f => e_map2 (@mul _) (Sem d e) (Sem d f)
  | f_div e f => LET e ::= Sem d e IN LET f ::= Sem d f IN mdiv d e f
  | f_sqrt e => LET e ::= Sem d e IN msqrt d e
  | f_id => mid
  | f_cos => mcos
  | f_sin => msin
  | f_cst e => e_map mcst (Sem d e)
  | f_trunc d e => e_map (mtruncate d) (Sem d e)
  | b_le e f => e_map2 is_le (Sem d e) (Sem d f)
  | b_ge e f => e_map2 is_ge (Sem d e) (Sem d f)
  | b_lt e f => e_map2 is_lt (Sem d e) (Sem d f)
  | b_ne e f => e_map2 is_ne (Sem d e) (Sem d f)
  | b_disj b c => LET b ::= Sem d b IN if b then ret true else Sem d c
  | b_conj b c => LET b ::= Sem d b IN if b then Sem d c else ret false
  | b_mlt _ _ _ _
  | b_mne _ _ _ _ => err "comparison of univariate functions not supported in static mode"
  | b_impl _ _ => err "cannot handle arbitrary implications"
  | b_forall _ => err "cannot handle arbitrary universal quantifications"
  | t_deg _ d x => Sem d x
  | t_var _ x => x
  | t_let _ _ x k => Sem d (k (Sem d x))
  end.
Definition Sem' d S (u: Term S): sval S := Sem d (u sval).

(** correctness of the above semantics
    the key lemma, [correct], is proved by induction on the parametricity relation *)
Definition cval S: sval S -> rval S -> Prop :=
  match S with
  | REAL => EP' contains
  | FUN  => EP' mcontains
  | BOOL => EPimpl
  end.
Lemma correct S (u: term S) (v: term S): trel cval u v -> forall d, cval (Sem d u) (sem v).
Proof.
  induction 1; intro deg; cbn in *.
  - eapply ep_map2; eauto. rel. 
  - eapply ep_map2; eauto. rel. 
  - eapply ep_map2; eauto. rel. 
  - constructor. rel. 
  - constructor. apply rfromQ. 
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
    by apply rmeval.
  - eapply ep_bind=>[F Ff|]; eauto.  
    eapply ep_bind=>[A Aa|]; eauto.  
    eapply ep_bind=>[B Bb|]; eauto.  
    apply rmintegrate; rel. 
  - eapply ep_map2; eauto. intros. by apply (radd (r:=mcontains)). 
  - eapply ep_map2; eauto. intros. by apply (rsub (r:=mcontains)). 
  - eapply ep_map2; eauto. intros. by apply (rmul (r:=mcontains)). 
  - eapply ep_bind=>[F Ff|]; eauto. 
    eapply ep_bind=>[G Gg|]; eauto.
    by apply rmdiv.
  - eapply ep_bind=>[F Ff|]; eauto.
    by apply rmsqrt.
  - apply rmid.
  - apply rmcos.
  - apply rmsin.
  - eapply ep_map; eauto. intros. by apply rmcst.          
  - eapply ep_map; eauto. intros. by apply rmtruncate.
  - eapply ep_map2; eauto. intros ??. case is_leE=>//. auto.  
  - eapply ep_map2; eauto. intros ??. case is_geE=>//. auto. 
  - eapply ep_map2; eauto. intros ??. case is_ltE=>//. auto.
  - eapply ep_map2; eauto. intros ??. case is_neE=>//. auto.
  - eapply ep_bind=>[b|]; eauto.  2: apply IHtrel1. 
    case b. constructor. tauto. intros _.
    case: IHtrel2=>//. constructor. tauto. 
  - eapply ep_bind=>[b|]; eauto. 2: apply IHtrel1.
    case b. case: IHtrel2=>//. constructor. auto. by constructor.
  - constructor. 
  - constructor.
  - by []. 
  - constructor. 
  - by []. 
  - assumption.
  - auto. 
Qed.

(** correctness on parametric (closed) terms follows *)
Lemma Correct: forall d S (u: Term S), parametric u -> cval (Sem' d u) (sem' u).
Proof. intros d S u U. apply correct, U. Qed.

  
(** small corollary, useful to obtain a tactic in tactic.v *)
Lemma check d (b: Term BOOL):
  parametric b ->
  (let b := Sem' d b in
   match b with ret b => is_true b | err s => False end) ->
  sem' b.
Proof. move: (@Correct d BOOL)=>/= C B. by case C. Qed.

End s.
Arguments check {_ _ _ _} _ _ _ _.
Arguments Sem {_} _ _ [_] _.

End Static.


(** ** dynamic evaluation function *)
(** where we choose the basis according to integral bounds *)
Module Dynamic.
Section s.

Context {N: NBH} (MO: II -> II -> ModelOps) (M: forall D: Domain, Model (MO dlo dhi) dlo dhi).

(** interpretation of expressions using intervals / models / booleans *)
Definition sval S :=
  match S with
  | REAL => E II
  | FUN => (forall MO: ModelOps, E MM)
  | BOOL => E bool
  end.
Fixpoint Sem d S (t: @term sval S): sval S :=
  match t in term S return sval S with
  | e_add e f => e_map2 (@add _) (Sem d e) (Sem d f)
  | e_sub e f => e_map2 (@sub _) (Sem d e) (Sem d f)
  | e_mul e f => e_map2 (@mul _) (Sem d e) (Sem d f)
  | e_div e f => e_map2 (@div _) (Sem d e) (Sem d f)
  | e_sqrt e => e_map (@sqrt _) (Sem d e)
  | e_cos e => e_map (@cos _) (Sem d e)
  | e_sin e => e_map (@sin _) (Sem d e)
  | e_abs e => e_map (@abs _) (Sem d e)
  | e_fromQ q => ret (fromQ q)
  | e_fromZ z => ret (fromZ z)
  | e_pi => ret pi
  | e_zer => ret 0
  | e_one => ret 1
  | e_eval f x => err "evaluation not yet supported in dynamic mode"
      (* LET f ::= Sem d f IN *)
      (* LET x ::= Sem d x IN  *)
      (* meval f x *)
  | e_integrate f a b => 
      LET a ::= Sem d a IN 
      LET b ::= Sem d b IN 
      if ~~ is_lt a b then err "dynamic: integral does not yield a valid domain" else
      LET f ::= Sem d f (MO a b) IN 
      mintegrate f None None
  | f_add e f => fun MO => e_map2 (@add _) (Sem d e MO) (Sem d f MO)
  | f_sub e f => fun MO => e_map2 (@sub _) (Sem d e MO) (Sem d f MO)
  | f_mul e f => fun MO => e_map2 (@mul _) (Sem d e MO) (Sem d f MO)
  | f_div e f => fun MO => LET e ::= Sem d e MO IN LET f ::= Sem d f MO IN mdiv d e f
  | f_sqrt e => fun MO => LET e ::= Sem d e MO IN msqrt d e
  | f_id => fun MO => mid
  | f_cos => fun MO => mcos
  | f_sin => fun MO => msin
  | f_cst e => fun MO => e_map mcst (Sem d e)
  | f_trunc d e => fun MO => e_map (mtruncate d) (Sem d e MO)
  | b_le e f => e_map2 is_le (Sem d e) (Sem d f)
  | b_ge e f => e_map2 is_ge (Sem d e) (Sem d f) 
  | b_lt e f => e_map2 is_lt (Sem d e) (Sem d f)
  | b_ne e f => e_map2 is_ne (Sem d e) (Sem d f)
  | b_disj b c => LET b ::= Sem d b IN if b then ret true else Sem d c
  | b_conj b c => LET b ::= Sem d b IN if b then Sem d c else ret false
  | b_mlt a b f g =>
      LET a ::= Sem d a IN 
      LET b ::= Sem d b IN
      if ~~ is_lt a b then err "invalid domain" else
      let M := MO a b in
      LET f ::= Sem d f M IN 
      LET g ::= Sem d g M IN
      mlt d f g
  | b_mne a b f g =>
      LET a ::= Sem d a IN 
      LET b ::= Sem d b IN
      if ~~ is_lt a b then err "invalid domain" else
      let M := MO a b in
      LET f ::= Sem d f M IN 
      LET g ::= Sem d g M IN
      ret (mne d f g)
  | b_impl _ _ => err "cannot handle arbitrary implications"
  | b_forall _ => err "cannot handle arbitrary universal quantifications"
  | t_deg _ d x => Sem d x
  | t_var _ x => x
  | t_let _ _ x k => Sem d (k (Sem d x))
  end.
Definition Sem' d S (u: Term S): sval S := Sem d (u sval).

(** correctness of the above semantics
    the key lemma, [correct], is proved by induction on the parametricity relation *)
Definition cval S: sval S -> rval S -> Prop :=
  match S with
  | REAL => EP' contains
  | FUN  => fun F f => forall MO a b (M: Model MO a b), EP' M (F MO) f
  | BOOL => EPimpl
  end.
Lemma correct S (u: term S) (v: term S): trel cval u v -> forall d, cval (Sem d u) (sem v).
Proof.
  induction 1; intro deg; cbn -[RInt] in *;
    try (intros MO' a b M';
         try specialize (IHtrel  _ _ _ M');
         try (specialize (IHtrel1  _ _ _ M'); specialize (IHtrel2  _ _ _ M'))).
  - eapply ep_map2; eauto. rel. 
  - eapply ep_map2; eauto. rel. 
  - eapply ep_map2; eauto. rel. 
  - constructor. rel. 
  - constructor. apply rfromQ. 
  - constructor. rel. 
  - constructor. rel. 
  - constructor. rel.
  - eapply ep_map2; eauto. rel. 
  - eapply ep_map; eauto. rel. 
  - eapply ep_map; eauto. rel. 
  - eapply ep_map; eauto. rel. 
  - eapply ep_map; eauto. rel. 
  - constructor. 
    (* eapply ep_bind=>[F Ff|]; eauto.  *)
    (* eapply ep_bind=>[X Xx|]; eauto. *)
    (* by apply rmeval. *)
  - eapply ep_bind=>[A Aa|]; eauto.  
    eapply ep_bind=>[B Bb|]; eauto.  
    case_eq (is_lt A B)=>[ab|]. 2: constructor.
    specialize (IHtrel1 deg _ _ _ (M (DfromI2 Aa Bb ab))).
    eapply ep_bind=>[F Ff|]; eauto.
    eapply rmintegrate; first apply Ff; by constructor. 
  - eapply ep_map2; eauto. intros. by apply (radd (r:=mcontains)).
  - eapply ep_map2; eauto. intros. by apply (rsub (r:=mcontains)).
  - eapply ep_map2; eauto. intros. by apply (rmul (r:=mcontains)). 
  - eapply ep_bind=>[F Ff|]; eauto. 
    eapply ep_bind=>[G Gg|]; eauto.
    by apply rmdiv.
  - eapply ep_bind=>[F Ff|]; eauto.
    by apply rmsqrt.
  - apply rmid.
  - apply rmcos.
  - apply rmsin.
  - eapply ep_map; eauto. intros. by apply rmcst.          
  - eapply ep_map; eauto. intros. by apply rmtruncate.          
  - eapply ep_map2; eauto. intros ??. case is_leE=>//. auto.  
  - eapply ep_map2; eauto. intros ??. case is_geE=>//. auto. 
  - eapply ep_map2; eauto. intros ??. case is_ltE=>//. auto.
  - eapply ep_map2; eauto. intros ??. case is_neE=>//. auto.
  - eapply ep_bind=>[b|]; eauto. 2: apply IHtrel1. 
    case b. constructor. left; auto. intros _.
    case: IHtrel2=>//. constructor. right; auto.
  - eapply ep_bind=>[b|]; eauto. 2: apply IHtrel1. 
    case b. case: IHtrel2=>//. constructor. auto. by constructor.
  - eapply ep_bind=>[A Aa|]; eauto.  
    eapply ep_bind=>[B Bb|]; eauto.  
    case_eq (is_lt A B)=>[ab|]. 2: constructor.
    specialize (IHtrel3 deg _ _ _ (M (DfromI2 Aa Bb ab))).
    specialize (IHtrel4 deg _ _ _ (M (DfromI2 Aa Bb ab))).
    eapply ep_bind=>[F Ff|]; eauto.
    eapply ep_bind=>[G Gg|]; eauto.
    eapply rmlt. apply Ff. apply Gg. 
  - eapply ep_bind=>[A Aa|]; eauto.  
    eapply ep_bind=>[B Bb|]; eauto.  
    case_eq (is_lt A B)=>[ab|]. 2: constructor.
    specialize (IHtrel3 deg _ _ _ (M (DfromI2 Aa Bb ab))).
    specialize (IHtrel4 deg _ _ _ (M (DfromI2 Aa Bb ab))).
    eapply ep_bind=>[F Ff|]; eauto.
    eapply ep_bind=>[G Gg|]; eauto.
    constructor. eapply rmne. apply Ff. apply Gg. 
  - by [].
  - constructor. 
  - by []. 
  - assumption.
  - auto. 
Qed.

(** correctness on parametric (closed) terms follows *)
Lemma Correct: forall d S (u: Term S), parametric u -> cval (Sem' d u) (sem' u).
Proof. intros d S u U. apply correct, U. Qed.

  
(** small corollary, useful to obtain a tactic in tactic.v *)
Lemma check d (b: Term BOOL):
  parametric b ->
  (let b := Sem' d b in
   match b with ret b => is_true b | err s => False end) ->
  sem' b.
Proof. move: (@Correct d BOOL)=>/= C B. by case C. Qed.

End s.
Arguments check {_ _} _ _ _.

End Dynamic.


(** ** notations for expressions *)
(** mostly used for tests in tests.v for now 
    sadly, trying to declare canonical structures of Ops0, Ops1, raises universe inconsistencies
 *)

Definition expr X := @term X REAL.
Definition fxpr X := @term X FUN.
Definition bxpr X := @term X BOOL.

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

Definition cst' X: expr X -> fxpr X := f_cst.
Coercion cst': expr >-> fxpr.
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
Definition truncate' X: Z -> fxpr X -> fxpr X := f_trunc.
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

Notation "'let_ee' x := e 'in' g" := (let' (e%expr: expr _) (fun (x: expr _) => (g%expr: expr _))) (at level 200, x binder, right associativity): expr_scope.
Notation "'let_ef' x := e 'in' g" := (let' (e%expr: expr _) (fun (x: expr _) => (g%fxpr: fxpr _))) (at level 200, x binder, right associativity): fxpr_scope.
Notation "'let_eb' x := e 'in' g" := (let' (e%expr: expr _) (fun (x: expr _) => (g%bxpr: bxpr _))) (at level 200, x binder, right associativity): bxpr_scope.
Notation "'let_fe' x := e 'in' g" := (let' (e%fxpr: fxpr _) (fun (x: fxpr _) => (g%expr: expr _))) (at level 200, x binder, right associativity): expr_scope.
Notation "'let_ff' x := e 'in' g" := (let' (e%fxpr: fxpr _) (fun (x: fxpr _) => (g%bxpr: fxpr _))) (at level 200, x binder, right associativity): fxpr_scope.
Notation "'let_fb' x := e 'in' g" := (let' (e%fxpr: fxpr _) (fun (x: fxpr _) => (g%bxpr: bxpr _))) (at level 200, x binder, right associativity): bxpr_scope.
Notation EXPR t := ((fun X => (t%expr: expr X)): Term REAL).
Notation FXPR t := ((fun X => (t%fxpr: fxpr X)): Term FUN).
Notation BXPR t := ((fun X => (t%bxpr: bxpr X)): Term BOOL).

(**
Check EXPR (1+e_pi).
Check EXPR (1+integrate' id' 0 1).
Check FXPR (id'/id').
Check EXPR (1+integrate' (id' / fsqrt id') 0 (fromQ' 3.3)).
Check EXPR (1+integrate' (id' / (fsqrt id' + fromQ' 3.2)) 0 (fromQ' 3.3)).
Check EXPR (let_ee x := 1+e_pi in x + x).
Check EXPR (let_ee x := 1+e_pi in x + let_ee y := x*x in sqrt' (y+y)).
Check FXPR (let_ef x := 1+e_pi in id' + x).
Check FXPR (let_ff f := 1-id' in id' * id').
Check BXPR (1 <= 0 \/ cos' pi' < 1 /\ cos' 0 >= 1).
Check BXPR (b_bounded_forall (fun c => integrate' (id'+cst' (t_var c)) 0 1 <= t_var c+1/fromZ' 2) 0%expr 1%expr).
*) 
