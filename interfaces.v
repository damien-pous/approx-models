(** * Interfaces for the library: basic operations, operations on functions, neighborhoods *)

Require Export QArith_base Psatz Rbase Rfunctions Ranalysis.
Require Export Coquelicot.Coquelicot.
Require Export Setoid Morphisms.
Require Export List. Export ListNotations.
Require Export ssreflect ssrbool ssrfun.
Require Export utils errors inrel.

Set Universe Polymorphism.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Close Scope Q_scope.
Open Scope R_scope.

(** ** preliminary tools *)

(** instances for setoid_rewriting on Rle *)
#[export] Instance Rle_PreOrder: PreOrder Rle.
Proof. constructor; cbv; intros; lra. Qed.
#[export] Instance Rlt_PreOrder: Transitive Rlt. 
Proof. cbv; intros; lra. Qed.
#[export] Instance Rlt_Rle: subrelation Rlt Rle.
Proof. cbv. tauto. Qed.
#[export] Instance Rplus_Rle: Proper (Rle ==> Rle ==> Rle) Rplus.
Proof. repeat intro. lra. Qed.

(** ssreflect notations for natural numbers *)
Notation "n .-1" := (Nat.pred n) (at level 2) : nat_scope.
Notation "n .+1" := (S n) (at level 2) : nat_scope.
Notation "n .+1" := (Z.succ n) (at level 2) : Z_scope.
Notation "n .+2" := n.+1.+1 (at level 2) : nat_scope.
Notation "n .+3" := n.+2.+1 (at level 2) : nat_scope.
Notation "n .+4" := n.+2.+2 (at level 2) : nat_scope.
Notation "n .+5" := n.+1.+4 (at level 2) : nat_scope.

(** injection from natural numbers to real numbers  *)
Notation INRS := S_INR.
Lemma INR0: INR O = 0. Proof. reflexivity. Qed.
Arguments INR: simpl nomatch.
Arguments RInt: simpl never.


(** blocking identity to document irrelevant values *)
Lemma IRRELEVANT (A: Type): A -> A.
Proof. by []. Qed. 



(** ** operations on scalars *)

(** basic operations *)
(** (will be instantiated on R, I, F, list C, Tube C) *)
Class Ops0 := {
  car: Type;
  add: car -> car -> car;
  sub: car -> car -> car;
  mul: car -> car -> car;
  mul': nat -> car -> car -> car;    (** truncated multiplication *)
  zer: car;
  one: car;
  mulZ: Z -> car -> car;
  divZ: Z -> car -> car;
  }.
Coercion car: Ops0 >-> Sortclass.

(** potentially truncated multiplication *)
Definition mul'' {C: Ops0} (d: option nat): C -> C -> C :=
  match d with None => mul | Some d => mul' d end.

(** extended operations *)
(** (will be instantiated on R, I, F) *)
Class Ops1 := {
  ops0: Ops0;
  fromZ: Z -> ops0;
  div: ops0 -> ops0 -> ops0;  (** also on Tube C, but with parameters *)
  sqrt: ops0 -> ops0;         (** idem *)
  cos: ops0 -> ops0;
  sin: ops0 -> ops0;
  abs: ops0 -> ops0;
  pi: ops0;
}.
Coercion ops0: Ops1 >-> Ops0.

(** notations *)
Declare Scope RO_scope.
Bind Scope RO_scope with car.
Infix "+" := add: RO_scope. 
Infix "*" := mul: RO_scope.
Notation "a *[ d  ] b" := (mul' d%nat a b) (at level 40, left associativity): RO_scope.
Notation "a *[. d  ] b" := (mul'' d%nat a b) (at level 40, left associativity): RO_scope.
Infix "-" := sub: RO_scope.
Infix "/" := div: RO_scope.
Notation "x // n" := (divZ n x) (at level 40, left associativity): RO_scope .
Notation "0" := zer: RO_scope.
Notation "1" := one: RO_scope.
Open Scope RO_scope.

(** derived operations *)
Definition fromN {C: Ops1} (n: nat): C := fromZ (Z.of_nat n). 
Definition fromQ {C: Ops1} (q: Q): C := divZ (Zpos (Qden q)) (fromZ (Qnum q)).
Arguments fromQ {_}: simpl never.

(* TOTHINK: powN, powP? *)
Fixpoint pow {C: Ops0} n (x: C) :=
  match n with
  | O => 1
  | S n => x*pow n x
  end.


(** ** lifting to functions *)
Definition f_cst A B (b: B) (a: A) := b.
Definition f_unr A B (o: B -> B) (f: A -> B) (a: A) := o (f a).
Definition f_bin A B (o: B -> B -> B) (f g: A -> B) (a: A) := o (f a) (g a).

Canonical Structure f_Ops0 (A: Type) (C: Ops0): Ops0 := {|
  car := A -> C;
  add := f_bin add;
  sub := f_bin sub;
  mul := f_bin mul;
  mul' z := f_bin (mul' z);
  zer := f_cst zer;
  one := f_cst one;
  mulZ z := f_unr (mulZ z);
  divZ z := f_unr (divZ z);
|}.
Canonical Structure f_Ops1 (A: Type) (C: Ops1): Ops1 := {|
  ops0 := f_Ops0 A C;
  fromZ z := f_cst (fromZ z);
  div := f_bin div;
  sqrt := f_unr sqrt;
  cos := f_unr cos;
  sin := f_unr sin;
  abs := f_unr abs;
  pi := f_cst pi;
|}.

(** tagged multiplication on reals, to indicate truncated multiplication request *)
Definition Rmult' (d: nat) := Rmult.
(** tagged identity, to indicate truncation requests *)
Definition Rtruncate (d: nat) (x: R) := x.


(** parameters for evaluating terms:
    - interpolation degree (for divisions, square roots, and model comparisons)
    - truncation degree, if any, for multiplications in validations
    - bisection depth (for universally quantified formulas and model comparisons)
 *)
Variant prm := degree of Z | trunc of option nat | depth of nat.
Record prms := Prms { p_deg: Z; p_trunc: option nat; p_depth: nat }.
Definition set_prm p ps :=
  match p with
  | degree d => {| p_deg := d; p_trunc := p_trunc ps; p_depth := p_depth ps |}
  | trunc d => {| p_deg := p_deg ps; p_trunc := d; p_depth := p_depth ps |}
  | depth d => {| p_deg := p_deg ps; p_trunc := p_trunc ps; p_depth := d |}
  end.
(** tagged identity, to indicate requested degrees/truncations in validation/bisection depth *)
Definition set (p: prm) [A] (x: A) := x.

(** ** instances on real numbers *)
Canonical Structure ROps0 := {|
  car := R;
  add := Rplus;
  sub := Rminus;
  mul := Rmult;
  mul' := Rmult';
  zer := R0;
  one := R1;
  mulZ z x := Rmult (IZR z) x;
  divZ z x := Rdiv x (IZR z);
|}.
Canonical Structure ROps1 := {|
  ops0 := ROps0;
  fromZ := IZR;
  div := Rdiv;
  sqrt := R_sqrt.sqrt;
  cos := Rtrigo_def.cos;
  sin := Rtrigo_def.sin;
  abs := Rabs;
  pi := Rtrigo1.PI;
|}.

Lemma RfromN: forall n, INR n = fromN n.
Proof INR_IZR_INZ.
Lemma RfromQ: forall q, Q2R q = fromQ q.
Proof. reflexivity. Qed.
Lemma RmulZ x z: IZR z * x = mulZ z x.
Proof. reflexivity. Qed.
Lemma RdivZ x z: x / IZR z = x // z.
Proof. reflexivity. Qed.

Lemma Rpow n x: x^n = pow n x.
Proof. induction n=>//=. congruence. Qed.


(** ** parametricity relations *)
(** convention: [opR] is the parametricity lemma for operation [op] *)
Class Rel0 (R S: Ops0) (mem: inRel R S) := {
  addR: ltac:(expand (add ∈ add));
  subR: ltac:(expand (sub ∈ sub));
  mulR: ltac:(expand (mul ∈ mul));
  (* note that we relate truncated multiplication to plain multiplication *)
  mul'R: forall d, ltac:(expand (mul ∈ mul' d));
  zerR: 0 ∈ 0;
  oneR: 1 ∈ 1;
  mulZR: forall z, ltac:(expand (mulZ z ∈ mulZ z));
  divZR: forall z, ltac:(expand (divZ z ∈ divZ z));
  (* addR: forall x y, x ∈ y -> forall x' y', x' ∈ y' -> x+x' ∈ y+y'; *)
  (* subR: forall x y, x ∈ y -> forall x' y', x' ∈ y' -> x-x' ∈ y-y'; *)
  (* mulR: forall x y, x ∈ y -> forall x' y', x' ∈ y' -> x*x' ∈ y*y'; *)
  (* (* note that we relate truncated multiplication to plain multiplication *) *)
  (* mul'R: forall d x y, x ∈ y -> forall x' y', x' ∈ y' -> x*x' ∈ y*[d]y'; *)
  (* zerR: 0 ∈ 0; *)
  (* oneR: 1 ∈ 1; *)
  (* mulZR: forall z x y, x ∈ y -> mulZ z x ∈ mulZ z y; *)
  (* divZR: forall z x y, x ∈ y -> divZ z x ∈ divZ z y; *)
}.
Class Rel1 (R S: Ops1) (mem: inRel R S) := {
  rel0:> Rel0 mem;
  fromZR: forall z, fromZ z ∈ fromZ z;
  divR: ltac:(expand (div ∈ div));
  sqrtR: ltac:(expand (sqrt ∈ sqrt));
  absR: ltac:(expand (abs ∈ abs));
  cosR: ltac:(expand (cos ∈ cos));
  sinR: ltac:(expand (sin ∈ sin));
  piR: pi ∈ pi;
  (* divR: forall x y, x ∈ y -> forall x' y', x' ∈ y' -> x/x' ∈ y/y'; *)
  (* sqrtR: forall x y, x ∈ y -> sqrt x ∈ sqrt y; *)
  (* absR: forall x y, x ∈ y -> abs x ∈ abs y; *)
  (* cosR: forall x y, x ∈ y -> cos x ∈ cos y; *)
  (* sinR: forall x y, x ∈ y -> sin x ∈ sin y; *)
  (* piR: pi ∈ pi; *)
}.

Global Hint Resolve rel0 addR subR mulR mul'R fromZR mulZR divZR zerR oneR divR sqrtR absR cosR sinR piR: rel.

(** parametricity of derived operations *)
Lemma powR `(Rel0) n: ltac:(expand (pow n ∈ pow n)).
Proof. induction n; rel. Qed.

Lemma mul''R `(Rel0) d: ltac:(expand (mul ∈ mul'' d)).
Proof. destruct d; rel. Qed.

Lemma fromNR `(Rel1) n: fromN n ∈ fromN n.
Proof. rel. Qed.

Lemma fromQR `(Rel1) q: fromQ q ∈ fromQ q.
Proof. rel. Qed.

Global Hint Resolve powR  mul''R fromNR fromQR: rel.



(** ** neighborhoods (effective abstractions for real numbers) *)

(** utilities for specifications *)
Variant minmax_spec [II] le {mem: inRel R II} (I: II): option II -> Prop :=
| minmax_spec_some: forall m M, m ∈ M -> m ∈ I -> (forall x, x ∈ I -> le x m) -> minmax_spec le I (Some M)
| minmax_spec_none: (forall x y, x ∈ I -> le x y -> y ∈ I)-> minmax_spec le I None.

(** neighborhoods: an abstract interface for computing with floating points and intervals 
    convention: 
    - uppercase letters for intervals, lowercase letters for real numbers
    - same letter when a real is assumed to belong to an interval: 
      y: R, Y: II   often means that we also have   H: y ∈ Y. 
    - [opE] is the main correctness/specification lemma for operation [op]
*)
Class NBH := {
  (** intervals *)
  II: Ops1;
  (** (parametric) membership relation *)
  mem:> inRel R II;
  mem1:> Rel1 mem;
  (** convexity of intervals  *)
  convex: forall x y Z, x ∈ Z -> y ∈ Z -> forall z, x<=z<=y -> z ∈ Z;
  (** additional operations on intervals *)
  interval: II -> II -> II;        (** `directed' convex hull *)
  max: II -> option II;    
  min: II -> option II;    
  full: II;                   (** [[-oo;+oo]] *)
  is_lt: II -> II -> bool; 
  is_le: II -> II -> bool;
  split: II -> II*II;         (** only used for bisection *)
  (** specification of the above operations; 
      together with convexity, [maxE] and [minE] entail that the elements of II always represent closed intervals. *)
  intervalE: forall x X, x ∈ X -> forall y Y, y ∈ Y -> forall z, x<=z<=y -> z ∈ interval X Y;
  maxE: forall X, minmax_spec Rle X (max X);
  minE: forall X, minmax_spec Rge X (min X);
  fullE: forall x, x ∈ full;
  is_ltE: forall X Y, is_lt X Y ~> forall x y, x ∈ X -> y ∈ Y -> x<y;
  is_leE: forall X Y, is_le X Y ~> forall x y, x ∈ X -> y ∈ Y -> x<=y;
  splitE: forall X, (fun '(Y,Z) => forall x, x ∈ X -> x ∈ Y \/ x ∈ Z) (split X);  
  (** (almost unspecified) floating point operations *)
  FF: Ops1;
  I2F: II -> FF;
  F2I: FF -> II;
  Fle: FF -> FF -> bool;
  Flt: FF -> FF -> bool;
  Fabs: FF -> FF;
  Fmax: FF -> FF -> FF;
  width: II -> FF;  (** width of an interval (unspecified, just for inspection) *)
  F2R: FF -> R;   (** needed to guarantee that F2I produces non-empty intervals *)
  F2IE: forall f, F2R f ∈ F2I f;
}.
Global Hint Resolve mem1 F2IE: rel.

(** derived operations and their specification *)
Definition mag {N: NBH} x: option II := max (abs x).
Definition sym {N: NBH} x: II := let x := abs x in interval (0-x) x.

Variant mag_spec [II] `{mem: inRel R II} (I: II): option II -> Prop :=
| mag_spec_some: forall m M, m ∈ M -> (forall x, x ∈ I -> Rabs x <= m) -> mag_spec I (Some M)
| mag_spec_none: mag_spec I None.

Lemma magE {N: NBH} X: mag_spec X (mag X).
Proof. rewrite /mag. case: maxE; econstructor; eauto; rel. Qed.

Lemma symE {N: NBH} x y I: Rabs x <= y -> y ∈ I -> x ∈ sym I.
Proof.
  intros Hx Hy. rewrite /sym. apply intervalE with (0-abs y) (abs y); try rel. 
  simpl; split_Rabs; lra.
Qed.

Definition is_ne {N: NBH} X Y := if is_lt X Y then true else is_lt Y X.
Lemma is_neE {N: NBH} X Y: is_ne X Y ~> forall x y, x ∈ X -> y ∈ Y -> x<>y.
Proof.
  apply implE. rewrite /is_ne.
  case is_ltE =>[H _ x y Xx Yy|]. 
  specialize (H _ _ Xx Yy). lra.
  case is_ltE=>[H _ x y Xx Yy|//].
  specialize (H _ _ Yy Xx). lra.
Qed.

Definition is_ge {N: NBH} X Y := is_le Y X.
Lemma is_geE {N: NBH} X Y: is_ge X Y ~> forall x y, x ∈ X -> y ∈ Y -> x>=y.
Proof. rewrite /is_ge. case is_leE; auto using Rle_ge. Qed.

(** bisection methods 
    - [bisect] operates on a single interval: the one to be bisected
    - [bisect2] operates on two intervals: the bounds of the one to be bisected *)
Fixpoint bisect {N: NBH} n (P: II -> E bool) (X: II): E bool :=
  match n with
  | 0 => ret false
  | S n => Eor (P X) (fun _ =>
                       let (Y,Z) := split X in
                       Eand (bisect n P Y) (fun _ => bisect n P Z))
  end.

Fixpoint bisect2 {N: NBH} n (P: II -> II -> E bool) (A B: II): E bool :=
  match n with
  | 0 => ret false
  | S n => Eor (P A B) (fun _ => 
                         let X := F2I (divZ 2 (I2F A + I2F B)) in
                         Eand (bisect2 n P A X) (fun _ => bisect2 n P X B))
  end.

Lemma bisectE {N: NBH} P (p: R -> Prop):
  (forall X, P X ~~> forall x, x ∈ X -> p x) ->
  forall n X, bisect n P X ~~> forall x, x ∈ X -> p x.
Proof.
  intro Pp. induction n=>X//=.
  apply: Eimpl_or'. apply Pp. 
  move: (splitE X). case split=>Y Z H.
  apply: Eimpl_and'; try apply: IHn.
  move=>HY HZ x Hx. case (H x Hx); eauto.
Qed.

Lemma bisect2E {N: NBH} P (p: R -> Prop):
  (forall A B, P A B ~~> forall x a b, a ∈ A -> b ∈ B -> a<=x<=b -> p x) ->
  forall n A B, bisect2 n P A B ~~> forall x a b, a ∈ A -> b ∈ B -> a<=x<=b -> p x.
Proof.
  intro Pp. induction n=>A B//=.
  set x' := divZ _ _. move: (F2IE x').
  set X := F2I _. set x := F2R _. move=>Xx.
  apply: Eimpl_or'. apply Pp.
  apply: Eimpl_and'; try apply: IHn.
  move=>AX XB y a b Aa Bb Hy.
  specialize (AX y _ _ Aa Xx). 
  specialize (XB y _ _ Xx Bb).
  have: y<=x \/ x<=y by lra. tauto. 
Qed.
  

(** ** [Model]: abstraction for functions on real numbers *)

(** operations on models *)
Class ModelOps {N: NBH} := {
  (** pointwise operations *)
  MM: Ops0;
  (** identity (maybe an error, since the identity may not belong to the considered base)*)
  mid: E MM;
  (** sine,cosine (idem) *)
  mcos: E MM;
  msin: E MM;
  (** constant function *)
  mcst: II -> MM;
  (** evaluation may raise errors, when the argument does not belong to the considered domain *)
  meval: MM -> II -> E II;
  (** integration; missing bounds are assumed to be those of the domain *)
  mintegrate: MM -> option II -> option II -> E II;
  (** division and square root: we use an certification a posteriori, 
      the first two arguments are the interpolation degree for the oracle and the truncation degree for the validation
      may raise errors, in case the oracles do not provide appropriate approximations
   *)
  mdiv: Z -> option nat -> MM -> MM -> E MM;
  msqrt: Z -> option nat -> MM -> E MM;
  (** [truncate] acts as the identity *)
  mtruncate: nat -> MM -> MM;
  (** [mrange] returns an approximation of the range of the model on the considered domain *)
  mrange: MM -> II;
  (** nullability/positivity test, first argument is supposed to be the interpolation degree for computing the inverse of the model in order get a well-conditionned problem 
      positivity test may raise an error, in case the given model is not declared as continuous
   *)
  mne0: Z -> MM -> bool;
  mgt0: Z -> MM -> E bool;
}.
Coercion MM: ModelOps >-> Ops0. 

Definition mlt `{ModelOps} z f g := mgt0 z (g-f).
Definition mle `{ModelOps} := mlt.
Definition mge `{ModelOps} z f g := mlt z g f.
Definition mne `{ModelOps} z f g := mne0 z (f-g).


(** predicate for specifying bounds of integrals (see [rmintegrate] below) *)
Variant omem {N: NBH} x: R -> option II -> Prop :=
| omem_some: forall a A, a ∈ A -> omem x a (Some A)
| omem_none: omem x x None.
Global Hint Constructors omem: rel.

(** specification of the above operations, on the domain [[lo;hi]] *)
Class Model {N: NBH} (MO: ModelOps) (lo hi: R) := {
  mmem:> inRel (R->R) MM;
  mmem0:> Rel0 mmem;
  midR: id ∈ mid;
  mcosR: cos ∈ mcos;
  msinR: sin ∈ msin;
  mcstR: forall c C, c ∈ C -> (fun _ => c) ∈ mcst C;
  mevalR: (fun f x => f x) ∈ meval; 
  mintegrateR: forall f F, f ∈ F ->
               forall a A, omem lo a A ->
               forall b B, omem hi b B ->
                      RInt f a b ∈ mintegrate F A B;
  mdivR: forall n t, div ∈ mdiv n t;
  msqrtR: forall n t, sqrt ∈ msqrt n t;
  mtruncateR: forall n, id ∈ mtruncate n;
  mrangeE: forall f F, f ∈ F -> forall x, lo<=x<=hi -> f x ∈ mrange F;
  mne0E: forall n F, mne0 n F ~> forall f, f ∈ F -> forall x, lo<=x<=hi -> f x <> 0;
  mgt0E: forall n F, mgt0 n F ~~> forall f, f ∈ F -> forall x, lo<=x<=hi -> 0 < f x;
}.
Global Hint Resolve mmem0 mcstR (* mevalR mevalR mintegrateR mdivR msqrtR *): rel.

Lemma mneE `{Model} n F G: mne n F G ~> forall f g, f ∈ F -> g ∈ G -> forall x, lo<=x<=hi -> f x <> g x.
Proof.
  apply implE. rewrite /mne. case mne0E=>//E _ f g Ff Gg x Hx. 
  apply Rminus_not_eq, (E (f-g))=>//=. rel.
Qed.

Lemma mltE `{Model} n F G: mlt n F G ~~> forall f g, f ∈ F -> g ∈ G -> forall x, lo<=x<=hi -> f x < g x.
Proof.
  rewrite /mlt EimplV. case mgt0E=>// E _ f g Ff Gg x Hx. 
  apply Rminus_gt_0_lt, (E (g-f))=>//=. rel. 
Qed.

Lemma mleE `{Model} n F G: mle n F G ~~> forall f g, f ∈ F -> g ∈ G -> forall x, lo<=x<=hi -> f x <= g x.
Proof. rewrite /mle EimplV. case mltE=>//. auto using Rlt_Rle. Qed.

Lemma mgeE `{Model} n F G: mge n F G ~~> forall f g, f ∈ F -> g ∈ G -> forall x, lo<=x<=hi -> f x >= g x.
Proof. rewrite /mge EimplV. case mleE=>//. auto using Rle_ge. Qed.


(** two instances of [rmulZ] and [rdivZ] that need to be explicited for the [rel] tactic to work well *)
Lemma mulZ'R {N: NBH} z x X: x ∈ X -> IZR z * x ∈ mulZ z X.
Proof. apply: mulZR. Qed.
Lemma divZ'R {N: NBH} z x X: x ∈ X -> x / IZR z ∈ divZ z X.
Proof. apply: divZR. Qed.
Global Hint Resolve mulZ'R divZ'R: rel.


(** ** domains *)

Class Domain_on C := make_domain_on {
  dlo: C;
  dhi: C;
}.

Class Domain {N: NBH} := make_domain {
  DR:> Domain_on R;
  DI:> Domain_on II;
  dloR: dlo ∈ dlo;
  dhiR: dhi ∈ dhi;
  dlohi: dlo<dhi;
}.
Global Hint Resolve dloR dhiR: rel.

(** constructing simple domains *)
(** from relative numbers *)
Definition DfromZ2 {N: NBH}(a b: Z) (H: Z.compare a b = Lt): Domain := {|
  DR := make_domain_on (fromZ a) (fromZ b);
  DI := make_domain_on (fromZ a) (fromZ b);
  dlohi := IZR_lt _ _ (proj1 (Z.compare_lt_iff _ _) H);
  dloR := fromZR a;
  dhiR := fromZR b;
|}.
Notation DZ2 a b := (@DfromZ2 _ a b eq_refl).

(** from rational numbers *)
Definition DfromQ2 {N: NBH}(a b: Q) (H: Qcompare a b = Lt): Domain := {|
  DR := make_domain_on (fromQ a) (fromQ b);
  DI := make_domain_on (fromQ a) (fromQ b);
  dlohi := Qreals.Qlt_Rlt _ _ (proj1 (Qlt_alt _ _) H);
  dloR := fromQR _ a;
  dhiR := fromQR _ b;
|}.
Notation DQ2 a b := (@DfromQ2 _ a b eq_refl).

(** from floating points *)
Program Definition DfromF2 {N: NBH}(a b: FF) (H: is_lt (F2I a) (F2I b)): Domain := {|
  DR := make_domain_on (F2R a) (F2R b);
  DI := make_domain_on (F2I a) (F2I b);
  dloR := F2IE a;
  dhiR := F2IE b;
|}.
Next Obligation.
  revert H. case is_ltE=>//H _. apply H; apply F2IE. 
Qed.
Notation DF2 a b := (@DfromF2 _ a b eq_refl).

(** from pointed intervals *)
Program Definition DfromI2 {N: NBH}(A B: II)(a b: R)
        (aA: a ∈ A)
        (bB: b ∈ B)
        (ab: is_lt A B): Domain := {|
  DR := make_domain_on a b;
  DI := make_domain_on A B;
  dloR := aA;
  dhiR := bB;
|}.
Next Obligation.
  revert ab. case is_ltE=>//; auto.
Qed.

Notation DI2 aA bB := (DfromI2 aA bB eq_refl).

