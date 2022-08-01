(** * Canonical membership relations *)

Require Export List. Export ListNotations.
Require Export ssreflect ssrbool ssrfun.
Require Export utils errors.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** a class to have a uniform membership notation for various relations:
    - membership of a real into an interval
    - pointwise membership of a list of reals into a list of intervals
    - membership of a function into a model
    - by extension, membership of an operation on reals/functions into an operation on intervals/models
    - and lifting of such relations across error-monadic values
 *)

Class inRel (R S: Type) := inrel: R -> S -> Prop. 
Infix "∈" := inrel (at level 70). 

(** associated decision tactic *)
Create HintDb rel discriminated.
Ltac rel := by repeat intro; eauto 100 with rel.

(** ** lifting relations to lists *)
Section r.
 
Context {R S: Type} {rel: inRel R S}.

Inductive list_rel: inRel (list R) (list S) :=
| nilR: [] ∈ []
| consR: forall x y h k, x ∈ y -> h ∈ k -> x::h ∈ y::k.
Global Existing Instance list_rel. 
Hint Constructors list_rel: rel.

Lemma tlR : forall h k , h ∈ k -> tl h ∈ tl k.
Proof. destruct 1; rel. Qed.

Lemma appR: forall h k, h ∈ k -> forall p q, p ∈ q -> h++p ∈ k++q.
Proof. induction 1; rel. Qed.

Lemma rev_appendR: forall h k, h ∈ k -> forall m n, m ∈ n -> rev_append h m ∈ rev_append k n.
Proof. induction 1; rel. Qed.

Lemma revR: forall h k, h ∈ k -> rev h ∈ rev k.
Proof. intros. apply rev_appendR; rel. Qed.

Lemma mapR A (f: A -> R) (g: A -> S):
  (forall a, f a ∈ g a) -> forall l, map f l ∈ map g l.
Proof. induction l; rel. Qed.

(** ** lifting relations to pairs *)

Global Instance pair_rel: inRel (R*R) (S*S) :=
  fun p q => rel p.1 q.1 /\ rel p.2 q.2.
Lemma pairR: forall p q, p ∈ q -> forall p' q', p' ∈ q' -> (p,p') ∈ (q,q').
Proof. by []. Qed.
Lemma proj1R p q: p ∈ q -> p.1 ∈ q.1.
Proof. by case. Qed.
Lemma proj2R p q: p ∈ q -> p.2 ∈ q.2.
Proof. by case. Qed.

(** ** lifting relations to options *)

Global Instance option_rel: inRel (option R) (option S) :=
  fun x y => match x,y with
          | Some x, Some y => x ∈ y
          | None, None => True
          | _,_ => False
          end.

(** ** lifting relations to error-monadic values *)
(** here we reuse the lifting operator from [errors]  *)
Global Instance error_rel: inRel (E R) (E S) := ER inrel. 

End r.
Global Hint Constructors list_rel: rel.
Global Hint Resolve tlR appR revR rev_appendR pairR proj1R proj2R: rel.


(** alternative lifting to error-monadic values, when one value remains pure *)
Global Instance error_rel' {A B} {mem: inRel A B}: inRel A (E B) := fun a => EP (mem a).



(** ** lifting relations to functions *)
(** this lifting is particularly important: 
    it allows us to use concise notations for specifying parametricity of polymorphic operations.
    For instance, in [interfaces], [add ∈ add] expands to [forall x X, x ∈ X -> forall y Y, y ∈ Y -> x+y ∈ X+Y].
 *)
Global Instance fun_rel {R R' S S'} {rel: inRel R S} {rel': inRel R' S'}: inRel (R->R') (S->S') :=
  fun f g => forall x y, x ∈ y -> f x ∈ g y.

(** explicit expansion of a membership relation using the above construct [fun_rel]
    we currently need this to add hints to the [rel] database: 
    a lemma of type [add ∈ add] cannot be used (sadly), only its type-expanded form can.
 *)
Ltac expand t :=
  let rec exp rel :=
    lazymatch rel with
    | @fun_rel ?R ?R' ?S ?S' ?rel0 ?rel1 =>
        let t := exp rel1 in
        uconstr:(fun f g => forall x y, @inrel _ _ rel0 x y -> t (f x) (g y))
    | ?t => uconstr:(@inrel _ _ t)
    end
  in lazymatch t with
     | @inrel _ _ ?rel ?f ?g => let rel := exp rel in
                      let t := constr:(rel f g) in
                      let t := eval hnf in t in
                        exact t
     end.

(** ** additional property of list lifting  *)
Lemma list_rel_map' {A B R S} `(inRel A B) `(inRel R S) (f: A -> R) (g: B -> S):
  (forall a b, a ∈ b -> f a ∈ g b) ->
  forall h k, h ∈ k -> map f h ∈ map g k.
Proof. intros ???. induction 1; rel. Qed.
