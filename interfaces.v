(** * Hierarchy of structures: basic operations, operations on functions, neighbourhoods *)

Require Export Psatz Rbase Rfunctions Ranalysis.
Require Export Coquelicot.Coquelicot.
Require Export Setoid Morphisms.
Require Export List. Export ListNotations.
Require Export ssreflect ssrbool ssrfun.
Require Import errors.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope R_scope.

(** ** preliminary tools *)

(** instances for setoid_rewriting on Rle *)
Instance Rle_PreOrder: PreOrder Rle.
Proof. constructor; cbv; intros; lra. Qed.
Instance Rlt_PreOrder: Transitive Rlt. 
Proof. cbv; intros; lra. Qed.
Instance Rlt_Rle: subrelation Rlt Rle.
Proof. cbv. tauto. Qed.
Instance Rplus_Rle: Proper (Rle ==> Rle ==> Rle) Rplus.
Proof. repeat intro. lra. Qed.

(** a few notations for natural numbers *)
Notation "n .-1" := (Nat.pred n) (at level 2) : nat_scope.
Notation "n .+1" := (S n) (at level 2) : nat_scope.
Notation "n .+2" := n.+1.+1 (at level 2) : nat_scope.
Notation "n .+3" := n.+2.+1 (at level 2) : nat_scope.
Notation "n .+4" := n.+2.+2 (at level 2) : nat_scope.
Notation "n .+5" := n.+1.+4 (at level 2) : nat_scope.

(** injection from natural numbers to real numbers  *)
Notation INRS := S_INR.
Lemma INR0: INR O = 0. Proof. reflexivity. Qed.

(** blocking identity to document irrelevant values *)
Lemma IRRELEVANT (A: Type): A -> A.
Proof. by []. Qed. 



(** ** Operations on scalars *)

(** basic operations *)
(** (will be instantiated on R, I, F, list C, Model C) *)
Record Ops0 := {
  car:> Type;
  add: car -> car -> car;
  sub: car -> car -> car;
  mul: car -> car -> car;
  zer: car;
  one: car;
}.

(** extended operations *)
(** (will be instantiated on R, I, F) *)
Record Ops1 := {
  ops0:> Ops0;
  fromZ: Z -> ops0;
  div: ops0 -> ops0 -> ops0;  (** also on Model C, but with parameters *)
  sqrt: ops0 -> ops0;         (** idem *)
  cos: ops0 -> ops0;
  abs: ops0 -> ops0;
  pi: ops0;
}.

(** derived operations *)
Definition fromN {C: Ops1} (n: nat) := fromZ C (Z.of_nat n). 
Definition dvn {C: Ops1} n x: C := div x (fromN n).

(** notations *)
Declare Scope RO_scope.
Infix "+" := add: RO_scope. 
Infix "*" := mul: RO_scope.
Infix "-" := sub: RO_scope.
Infix "/" := div: RO_scope.
Notation "x // n" := (dvn n x) (at level 40, left associativity): RO_scope .
Notation "0" := (zer _): RO_scope.
Notation "1" := (one _): RO_scope.
Arguments fromZ {_}. 
Arguments pi {_}. 
Open Scope RO_scope.
Bind Scope RO_scope with car.

(** derived operations *)
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
  zer := f_cst (@zer C);
  one := f_cst (@one C);
|}.

(** ** instances on Reals *)
Canonical Structure ROps0 := {|
  car := R;
  add := Rplus;
  sub := Rminus;
  mul := Rmult;
  zer := R0;
  one := R1;
|}.
Canonical Structure ROps1 := {|
  ops0 := ROps0;
  fromZ := IZR;
  div := Rdiv;
  sqrt := R_sqrt.sqrt;
  cos := Rtrigo_def.cos;
  abs := Rabs;
  pi := Rtrigo1.PI;
|}.
Lemma RfromN: forall n, INR n = fromN n.
Proof INR_IZR_INZ.
Lemma Rpow n x: x^n = pow n x.
Proof. induction n=>//=. congruence. Qed.

(** ** parametricity relations *)
Record Rel0 (R S: Ops0) := {
  rel:> R -> S -> Prop;
  radd: forall x y, rel x y -> forall x' y', rel x' y' -> rel (x+x') (y+y');
  rsub: forall x y, rel x y -> forall x' y', rel x' y' -> rel (x-x') (y-y');
  rmul: forall x y, rel x y -> forall x' y', rel x' y' -> rel (x*x') (y*y');
  rzer: rel 0 0;
  rone: rel 1 1
}.
Record Rel1 (R S: Ops1) := {
  rel0:> Rel0 R S;
  rdiv: forall x y, rel0 x y -> forall x' y', rel0 x' y' -> rel0 (x/x') (y/y');
  rfromZ: forall z, rel0 (fromZ z) (fromZ z);
  rsqrt: forall x y, rel0 x y -> rel0 (sqrt x) (sqrt y);
  rabs: forall x y, rel0 x y -> rel0 (abs x) (abs y);
  rcos: forall x y, rel0 x y -> rel0 (cos x) (cos y);
  rpi: rel0 pi pi;
}.
Global Hint Resolve radd rsub rmul rfromZ rzer rone rdiv rsqrt rabs rcos rpi: rel.
Ltac rel := by eauto 100 with rel.

(** parametricity of derived operations *)
Lemma rpow R S (T: Rel0 R S) n: forall x y, T x y -> T (pow n x) (pow n y).
Proof. induction n; simpl; rel. Qed.
Global Hint Resolve rpow: rel.

Lemma rfromN R S (T: Rel1 R S) n: T (fromN n) (fromN n).
Proof. unfold fromN; rel. Qed.
Global Hint Resolve rfromN: rel.

Lemma rdvn R S (T: Rel1 R S) n: forall x y, T x y -> T (x//n) (y//n).
Proof. rewrite /dvn; rel. Qed.
Global Hint Resolve rdvn: rel.


(** ** Neighborhoods (effective abstractions for real numbers) *)

(** utilities for specifications  *)
Inductive minmax_spec A le (contains: A -> R -> Prop) (a: A): option A -> Prop :=
| minmax_spec_some: forall m b, contains m b -> contains a b -> (forall x, contains a x -> le x b) -> minmax_spec le contains a (Some m)
| minmax_spec_none: (forall x y, contains a x -> le x y -> contains a y)-> minmax_spec le contains a None.

Inductive wreflect (P : Prop): bool -> Prop :=
 | wReflectT: P -> wreflect P true | wReflectF: wreflect P false.

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
  bnd: II -> II -> II;
  max: II -> option II;    
  min: II -> option II;    
  bot: II;                   (** [-oo;+oo] *)
  is_lt: II -> II -> bool; 
  is_le: II -> II -> bool;
  (** specification of the above operations *)
  bndE: forall X x, contains X x -> forall Y y, contains Y y -> forall z, x<=z<=y -> contains (bnd X Y) z;
  maxE: forall X, minmax_spec Rle contains X (max X);
  minE: forall X, minmax_spec Rge contains X (min X);
  botE: forall x, contains bot x;
  is_ltE: forall X Y, wreflect (forall x y, contains X x -> contains Y y -> x<y) (is_lt X Y);
  is_leE: forall X Y, wreflect (forall x y, contains X x -> contains Y y -> x<=y) (is_le X Y);
  (** (almost unspecified) floating point operations *)
  FF: Ops1;
  I2F: II -> FF;
  F2I: FF -> II;
  width: II -> FF;  (** width of an interval (unspecified, just for inspection) *)
  F2R: FF -> R;   (** needed to guarantee that F2I produces non-empty intervals *)
  F2IE: forall f, contains (F2I f) (F2R f);
  (** is an interval contained within the given bounds? (needed only in the very end, for concrete examples) *)
  subseteq: II -> R -> R -> Prop; (** note that this one is in Prop  *)
  subseteqE: forall X (a b: R), subseteq X a b -> forall x, contains X x -> a <= x <= b;
}.
Coercion II: NBH >-> Ops1.

(** derived operations and their specification *)
Definition mag {N: NBH} x: option II := max (abs x).
Definition sym {N: NBH} x: II := let x := abs x in bnd (0-x) x.

Inductive mag_spec A (contains: A -> R -> Prop) (a: A): option A -> Prop :=
| mag_spec_some: forall m b, contains m b -> (forall x, contains a x -> Rabs x <= b) -> mag_spec contains a (Some m)
| mag_spec_none: mag_spec contains a None.

Lemma magE {N: NBH} X: mag_spec contains X (mag X).
Proof. rewrite /mag. elim: maxE; econstructor; eauto; rel. Qed.

Lemma symE {N: NBH} x y I: Rabs x <= y -> contains I y -> contains (sym I) x.
Proof.
  intros Hx Hy. rewrite /sym. apply bndE with (0-abs y) (abs y); try rel. 
  simpl; split_Rabs; lra.
Qed.

(** predicate for specifying bounds of integrals (see [rmintegrate] below) *)
Inductive ocontains{N: NBH} x: option II -> R -> Prop :=
| ocontains_some: forall A a, contains A a -> ocontains x (Some A) a
| ocontains_none: ocontains x None x.
Global Hint Constructors ocontains: rel.

(** ** domains *)

Class Domain_on C := make_domain {
  lo: C;
  hi: C;
}.

Class Domain {N: NBH} := {
  DR:> Domain_on R;
  DI:> Domain_on II;
  DF:> Domain_on FF;
  lohi: lo<hi;
  rlo: contains lo lo;
  rhi: contains hi hi;
}.
Global Hint Resolve rlo rhi: rel.

Definition dom `{Domain} (x: R) := lo <= x <= hi.
Definition Dom `{Domain} (X: II) := is_le lo X && is_le X hi.

Lemma DomE `{Domain} X: wreflect (forall x, contains X x -> dom x) (Dom X).
Proof.
  rewrite /Dom.
  case is_leE=>[Lo|]. 2: constructor. 
  case is_leE=>[Hi|]; constructor=> x Xx.
  split; [apply Lo|apply Hi]=>//. apply rlo. apply rhi.
Qed.


(** constructing simple domains *)
(** from relative numbers *)
Definition DfromZ2 {N: NBH}(a b: Z) (H: Z.compare a b = Lt): Domain := {|
  DR := make_domain (fromZ a) (fromZ b);
  DI := make_domain (fromZ a) (fromZ b);
  DF := make_domain (fromZ a) (fromZ b);
  lohi := IZR_lt _ _ (proj1 (Z.compare_lt_iff _ _) H);
  rlo := rfromZ _ a;
  rhi := rfromZ _ b;
|}.
Notation DZ2 a b := (@DfromZ2 _ a b eq_refl).

(** from floating points *)
Program Definition DfromF2 {N: NBH}(a b: FF) (H: is_lt (F2I a) (F2I b)): Domain := {|
  DR := make_domain (F2R a) (F2R b);
  DI := make_domain (F2I a) (F2I b);
  DF := make_domain a b;
  rlo := F2IE a;
  rhi := F2IE b;
|}.
Next Obligation.
  revert H. case is_ltE=>//H _. apply H; apply F2IE. 
Qed.
Notation DF2 a b := (@DfromF2 _ a b eq_refl).

(** from intervals *)
Definition DfromI2 {N: NBH}(a b: II) := @DfromF2 N (I2F a) (I2F b).
Notation DI2 a b := (@DfromI2 _ a b eq_refl).


(** ** FunOps: abstraction for functions on real numbers *)

Class FunOps {N: NBH} := {
  (* domain of the considered functions *)
  mdom:> Domain;
  
  (* pointwise operations *)
  MM: Ops0;
  (* operations specific to functions *)
  mid: MM;                 
  mcst: II -> MM;
  meval: MM -> II -> E II;
  (* integration; missing bounds are assumed to be those of the domain *)
  mintegrate: MM -> option II -> option II -> E II;
  mdiv: Z -> MM -> MM -> E MM;
  msqrt: Z -> MM -> E MM;
  (* [truncate] acts as the identity *)
  mtruncate: nat -> MM -> MM;
  mrange: MM -> II;

  (* specification *)
  mcontains: Rel0 MM (f_Ops0 R ROps0);
  rmid: mcontains mid id;
  rmcst: forall C c, contains C c -> mcontains (mcst C) (fun _ => c);
  rmeval: forall F f, mcontains F f ->
          forall X x, contains X x -> 
                      EP' contains (meval F X) (f x);
  rmintegrate: forall F f, mcontains F f -> (forall x, dom x -> continuity_pt f x) ->
               forall A a, ocontains lo A a ->
               forall C c, ocontains hi C c ->
                           EP' contains (mintegrate F A C) (RInt f a c);
  rmdiv: forall n F f, mcontains F f ->
         forall   G g, mcontains G g -> 
                       EP' mcontains (mdiv n F G) (f_bin Rdiv f g);
  rmsqrt: forall n F f, mcontains F f ->
                        EP' mcontains (msqrt n F) (f_unr R_sqrt.sqrt f);
  rmtruncate: forall n F f, mcontains F f ->
                            mcontains (mtruncate n F) f;
  rmrange: forall F f, mcontains F f ->
           forall x, dom x -> contains (mrange F) (f x);
}.
Coercion MM: FunOps >-> Ops0.
Coercion mcontains: FunOps >-> Rel0.
Global Hint Resolve rmid rmcst rmeval rmintegrate rmdiv rmsqrt: rel.

