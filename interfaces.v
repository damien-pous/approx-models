(** * Hierarchy of structures: basic operations, operations on functions, neighbourhoods *)

Require Export QArith_base Psatz Rbase Rfunctions Ranalysis.
Require Export Coquelicot.Coquelicot.
Require Export Setoid Morphisms.
Require Export List. Export ListNotations.
Require Export ssreflect ssrbool ssrfun.
Require Export utils errors.

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

(** a few notations for natural numbers *)
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
Arguments INR _: simpl nomatch.


(** blocking identity to document irrelevant values *)
Lemma IRRELEVANT (A: Type): A -> A.
Proof. by []. Qed. 



(** ** operations on scalars *)

(** basic operations *)
(** (will be instantiated on R, I, F, list C, Tube C) *)
Record Ops0 := {
  car:> Type;
  add: car -> car -> car;
  sub: car -> car -> car;
  mul: car -> car -> car;
  mul': nat -> car -> car -> car;    (* truncated multiplication *)
  zer: car;
  one: car;
  mulZ: Z -> car -> car;
  divZ: Z -> car -> car;
  }.
Definition mul'' {C: Ops0} d :=
  match d with None => @mul C | Some d => @mul' C d end.

(** extended operations *)
(** (will be instantiated on R, I, F) *)
Record Ops1 := {
  ops0:> Ops0;
  fromZ: Z -> ops0;
  div: ops0 -> ops0 -> ops0;  (** also on Tube C, but with parameters *)
  sqrt: ops0 -> ops0;         (** idem *)
  cos: ops0 -> ops0;
  sin: ops0 -> ops0;
  abs: ops0 -> ops0;
  pi: ops0;
}.

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
Notation "0" := (zer _): RO_scope.
Notation "1" := (one _): RO_scope.
Arguments fromZ {_}. 
Arguments mulZ {_}. 
Arguments divZ {_}. 
Arguments sqrt {_}. 
Arguments cos {_}. 
Arguments sin {_}. 
Arguments abs {_}. 
Arguments pi {_}. 
Open Scope RO_scope.

(** derived operations *)
Definition fromN {C: Ops1} (n: nat): C := fromZ (Z.of_nat n). 
Definition fromQ {C: Ops1} (q: Q): C := divZ (Zpos (Qden q)) (fromZ (Qnum q)).

(* TOTHINK: powN, powP? *)
Fixpoint pow (C: Ops0) n (x: C) :=
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
  add := f_bin (@add C);
  sub := f_bin (@sub C);
  mul := f_bin (@mul C);
  mul' z := f_bin (mul' z);
  zer := f_cst (@zer C);
  one := f_cst (@one C);
  mulZ z := f_unr (mulZ z);
  divZ z := f_unr (divZ z);
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

(* TOTHINK: efficiency? *)
Lemma Rpow n x: x^n = pow n x.
Proof. induction n=>//=. congruence. Qed.

(** ** parametricity relations *)
Record Rel0 (R S: Ops0) := {
  rel:> R -> S -> Prop;
  radd: forall x y, rel x y -> forall x' y', rel x' y' -> rel (x+x') (y+y');
  rsub: forall x y, rel x y -> forall x' y', rel x' y' -> rel (x-x') (y-y');
  rmul: forall x y, rel x y -> forall x' y', rel x' y' -> rel (x*x') (y*y');
  (* note that we relate truncated multiplication to plain multiplication *)  
  rmul': forall d x y, rel x y -> forall x' y', rel x' y' -> rel (x*[d]x') (y*y'); 
  rzer: rel 0 0;
  rone: rel 1 1;
  rmulZ: forall z x y, rel x y -> rel (mulZ z x) (mulZ z y);
  rdivZ: forall z x y, rel x y -> rel (divZ z x) (divZ z y);
}.
Record Rel1 (R S: Ops1) := {
  rel0:> Rel0 R S;
  rfromZ: forall z, rel0 (fromZ z) (fromZ z);
  rdiv: forall x y, rel0 x y -> forall x' y', rel0 x' y' -> rel0 (x/x') (y/y');
  rsqrt: forall x y, rel0 x y -> rel0 (sqrt x) (sqrt y);
  rabs: forall x y, rel0 x y -> rel0 (abs x) (abs y);
  rcos: forall x y, rel0 x y -> rel0 (cos x) (cos y);
  rsin: forall x y, rel0 x y -> rel0 (sin x) (sin y);
  rpi: rel0 pi pi;
}.
Create HintDb rel discriminated.
Global Hint Resolve radd rsub rmul rmul' rfromZ rmulZ rdivZ rzer rone rdiv rsqrt rabs rcos rsin rpi: rel.
Ltac rel := by eauto 100 with rel.

(** parametricity of derived operations *)
Lemma rpow R S (T: Rel0 R S) n: forall x y, T x y -> T (pow n x) (pow n y).
Proof. induction n; simpl; rel. Qed.
Global Hint Resolve rpow: rel.

Lemma rfromN R S (T: Rel1 R S) n: T (fromN n) (fromN n).
Proof. unfold fromN; rel. Qed.
Global Hint Resolve rfromN: rel.

Lemma rfromQ R S (T: Rel1 R S) q: T (fromQ q) (fromQ q).
Proof. unfold fromQ; rel. Qed.
Global Hint Resolve rfromQ: rel.

Lemma rmul'' R S (T: Rel0 R S): forall d x y, T x y -> forall x' y', T x' y' -> T (x*[.d]x') (y*y').
Proof. destruct d; rel. Qed.
Global Hint Resolve rmul'': rel.


(** ** neighborhoods (effective abstractions for real numbers) *)

(** utilities for specifications *)
Variant minmax_spec A le (contains: A -> R -> Prop) (a: A): option A -> Prop :=
| minmax_spec_some: forall m b, contains m b -> contains a b -> (forall x, contains a x -> le x b) -> minmax_spec le contains a (Some m)
| minmax_spec_none: (forall x y, contains a x -> le x y -> contains a y)-> minmax_spec le contains a None.

(** neighborhoods: an abstract interface for computing with floating points and intervals 
    convention: 
    - uppercase letters for intervals, lowercase letters for real numbers
    - same letter when a real is assumed to belong to an interval: 
      y: R, Y: II   often means that we also have   H: contains Y y. *)
Class NBH := {
  (** intervals *)
  II: Ops1;
  (** (parametric) containment relation *)
  contains: Rel1 II ROps1;
  (** convexity of intervals  *)
  convex: forall Z x y, contains Z x -> contains Z y -> forall z, x<=z<=y -> contains Z z;
  (** additional operations on intervals *)
  bnd: II -> II -> II;        (** `directed' convex hull *)
  max: II -> option II;    
  min: II -> option II;    
  bot: II;                   (** [[-oo;+oo]] *)
  is_lt: II -> II -> bool; 
  is_le: II -> II -> bool;
  split: II -> II*II;         (** only used for bisection *)
  (** specification of the above operations; 
      together with convexity, [maxE] and [minE] entail that the elements of II always represent closed intervals *)
  bndE: forall X x, contains X x -> forall Y y, contains Y y -> forall z, x<=z<=y -> contains (bnd X Y) z;
  maxE: forall X, minmax_spec Rle contains X (max X);
  minE: forall X, minmax_spec Rge contains X (min X);
  botE: forall x, contains bot x;
  is_ltE: forall X Y, impl (is_lt X Y) (forall x y, contains X x -> contains Y y -> x<y);
  is_leE: forall X Y, impl (is_le X Y) (forall x y, contains X x -> contains Y y -> x<=y);
  splitE: forall X, (fun '(Y,Z) => forall x, contains X x -> contains Y x \/ contains Z x) (split X);  
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
  F2IE: forall f, contains (F2I f) (F2R f);
}.
Coercion II: NBH >-> Ops1.
Global Hint Resolve F2IE: rel.

(** derived operations and their specification *)
Definition mag {N: NBH} x: option II := max (abs x).
Definition sym {N: NBH} x: II := let x := abs x in bnd (0-x) x.

Variant mag_spec A (contains: A -> R -> Prop) (a: A): option A -> Prop :=
| mag_spec_some: forall m b, contains m b -> (forall x, contains a x -> Rabs x <= b) -> mag_spec contains a (Some m)
| mag_spec_none: mag_spec contains a None.

Lemma magE {N: NBH} X: mag_spec contains X (mag X).
Proof. rewrite /mag. case: maxE; econstructor; eauto; rel. Qed.

Lemma symE {N: NBH} x y I: Rabs x <= y -> contains I y -> contains (sym I) x.
Proof.
  intros Hx Hy. rewrite /sym. apply bndE with (0-abs y) (abs y); try rel. 
  simpl; split_Rabs; lra.
Qed.

Definition is_ne {N: NBH} X Y := if is_lt X Y then true else is_lt Y X.
Lemma is_neE {N: NBH} X Y: impl (is_ne X Y) (forall x y, contains X x -> contains Y y -> x<>y).
Proof.
  rewrite /is_ne. case is_ltE=>[H|].
  constructor=>x y Xx Yy. specialize (H _ _ Xx Yy). lra.
  case is_ltE=>[H|]; constructor=> x y Xx Yy. specialize (H _ _ Yy Xx). lra.
Qed.

Definition is_ge {N: NBH} X Y := is_le Y X.
Lemma is_geE {N: NBH} X Y: impl (is_ge X Y) (forall x y, contains X x -> contains Y y -> x>=y).
Proof. rewrite /is_ge. case is_leE=>[H|]; constructor; auto using Rle_ge. Qed.

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
  (forall X, Eimpl (P X) (forall x, contains X x -> p x)) ->
  forall n X, Eimpl (bisect n P X) (forall x, contains X x -> p x).
Proof.
  intro Pp. induction n=>X//=.
  apply Eimpl_or'=>//.
  move: (splitE X). case split=>Y Z H.
  eapply Eimpl_and'=>//HY HZ x Hx.
  case (H x Hx); eauto.
Qed.

Lemma bisect2E {N: NBH} P (p: R -> Prop):
  (forall A B, Eimpl (P A B) (forall x a b, contains A a -> contains B b -> a<=x<=b -> p x)) ->
  forall n A B, Eimpl (bisect2 n P A B) (forall x a b, contains A a -> contains B b -> a<=x<=b -> p x).
Proof.
  intro Pp. induction n=>A B//=.
  set x' := divZ _ _. move: (F2IE x').
  set X := F2I _. set x := F2R _. move=>Xx.
  apply Eimpl_or'=>//.
  eapply Eimpl_and'=>//AX XB y a b Aa Bb Hy.
  specialize (AX y _ _ Aa Xx). 
  specialize (XB y _ _ Xx Bb).
  have: y<=x \/ x<=y by lra. tauto. 
Qed.
  
(** predicate for specifying bounds of integrals (see [rmintegrate] below) *)
Variant ocontains{N: NBH} x: option II -> R -> Prop :=
| ocontains_some: forall A a, contains A a -> ocontains x (Some A) a
| ocontains_none: ocontains x None x.
Global Hint Constructors ocontains: rel.
  

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
Definition mne `{ModelOps} z f g := mne0 z (f-g).

(** specification of the above operations, on the domain [[lo;hi]] *)
Class Model {N: NBH} (MO: ModelOps) (lo hi: R) := {
  mcontains: Rel0 MM (f_Ops0 R ROps0);
  rmid: EP' mcontains mid id;
  rmcos: EP' mcontains mcos cos;
  rmsin: EP' mcontains msin sin;
  rmcst: forall C c, contains C c -> mcontains (mcst C) (fun _ => c);
  rmeval: forall F f, mcontains F f ->
          forall X x, contains X x -> 
                 EP' contains (meval F X) (f x);
  rmintegrate: forall F f, mcontains F f ->
               forall A a, ocontains lo A a ->
               forall C c, ocontains hi C c ->
                           EP' contains (mintegrate F A C) (RInt f a c);
  rmdiv: forall n t F f, mcontains F f ->
             forall G g, mcontains G g -> 
                    EP' mcontains (mdiv n t F G) (fun x => f x / g x);
  rmsqrt: forall n t F f, mcontains F f ->
                     EP' mcontains (msqrt n t F) (fun x => sqrt (f x));
  rmtruncate: forall n F f, mcontains F f ->
                            mcontains (mtruncate n F) f;
  rmrange: forall F f, mcontains F f ->
           forall x, lo<=x<=hi -> contains (mrange F) (f x);
  rmne0: forall n F f, mcontains F f -> impl (mne0 n F) (forall x, lo<=x<=hi -> f x <> 0);
  rmgt0: forall n F f, mcontains F f -> Eimpl (mgt0 n F) (forall x, lo<=x<=hi -> 0 < f x);
}.
Coercion mcontains: Model >-> Rel0.
Global Hint Resolve rmcst (* rmeval rmintegrate rmdiv rmsqrt *): rel.

Lemma rmne `{Model} n F f G g: mcontains F f -> mcontains G g ->
                               impl (mne n F G) (forall x, lo<=x<=hi -> f x <> g x).
Proof.
  rewrite /mne=>Ff Gg. ecase rmne0=>//. rel.
  intro C. constructor=>??. by apply Rminus_not_eq, C.
Qed.

Lemma rmlt `{Model} n F f G g: mcontains F f -> mcontains G g ->
                               Eimpl (mlt n F G) (forall x, lo<=x<=hi -> f x < g x).
Proof.
  rewrite /mlt=>Ff Gg. ecase rmgt0=>//. rel.
  intros a E. rewrite EimplR. case E=>//C. constructor=>x Hx.
  by apply Rminus_gt_0_lt, C.
Qed.

(** two instances of [rmulZ] and [rdivZ] that need to be explicited for the [rel] tactic to work well *)
Lemma rmulZ' {N: NBH} z x y: contains x y -> contains (mulZ z x) (IZR z * y).
Proof. apply rmulZ. Qed.
Lemma rdivZ' {N: NBH} z x y: contains x y -> contains (divZ z x) (y / IZR z).
Proof. apply rdivZ. Qed.
Global Hint Resolve rmulZ' rdivZ': rel.


(** ** domains *)

Class Domain_on C := make_domain_on {
  dlo: C;
  dhi: C;
}.

Class Domain {N: NBH} := make_domain {
  DR:> Domain_on R;
  DI:> Domain_on II;
  rdlo: contains dlo dlo;
  rdhi: contains dhi dhi;
  dlohi: dlo<dhi;
}.
Global Hint Resolve rdlo rdhi: rel.

(** constructing simple domains *)
(** from relative numbers *)
Definition DfromZ2 {N: NBH}(a b: Z) (H: Z.compare a b = Lt): Domain := {|
  DR := make_domain_on (fromZ a) (fromZ b);
  DI := make_domain_on (fromZ a) (fromZ b);
  dlohi := IZR_lt _ _ (proj1 (Z.compare_lt_iff _ _) H);
  rdlo := rfromZ _ a;
  rdhi := rfromZ _ b;
|}.
Notation DZ2 a b := (@DfromZ2 _ a b eq_refl).

(** from rational numbers *)
Definition DfromQ2 {N: NBH}(a b: Q) (H: Qcompare a b = Lt): Domain := {|
  DR := make_domain_on (fromQ a) (fromQ b);
  DI := make_domain_on (fromQ a) (fromQ b);
  dlohi := Qreals.Qlt_Rlt _ _ (proj1 (Qlt_alt _ _) H);
  rdlo := rfromQ _ a;
  rdhi := rfromQ _ b;
|}.
Notation DQ2 a b := (@DfromQ2 _ a b eq_refl).

(** from floating points *)
Program Definition DfromF2 {N: NBH}(a b: FF) (H: is_lt (F2I a) (F2I b)): Domain := {|
  DR := make_domain_on (F2R a) (F2R b);
  DI := make_domain_on (F2I a) (F2I b);
  rdlo := F2IE a;
  rdhi := F2IE b;
|}.
Next Obligation.
  revert H. case is_ltE=>//H _. apply H; apply F2IE. 
Qed.
Notation DF2 a b := (@DfromF2 _ a b eq_refl).

(** from pointed intervals *)
Program Definition DfromI2 {N: NBH}(A B: II)(a b: R)
        (Aa: contains A a)
        (Bb: contains B b)
        (ab: is_lt A B): Domain := {|
  DR := make_domain_on a b;
  DI := make_domain_on A B;
  rdlo := Aa;
  rdhi := Bb;
|}.
Next Obligation.
  revert ab. case is_ltE=>//; auto.
Qed.

Notation DI2 Aa Bb := (DfromI2 Aa Bb eq_refl).

