(** * Operations on linear combinations (generalised polynomials) *)

Require Export interfaces.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** lifting relations to lists and pairs *)
Section r.
 
Variables R S: Type.
Variable rel: R -> S -> Prop.

Inductive list_rel: list R -> list S -> Prop :=
| rnil: list_rel [] []
| rcons: forall x y h k, rel x y -> list_rel h k -> list_rel (x::h) (y::k).
Hint Constructors list_rel: rel.

Lemma list_rel_app: forall h k, list_rel h k -> forall p q, list_rel p q -> list_rel (h++p) (k++q).
Proof. induction 1; simpl; rel. Qed.
Hint Resolve list_rel_app: rel.

Lemma list_rel_rev: forall h k, list_rel h k -> list_rel (rev h) (rev k).
Proof. induction 1; rewrite /= /rev /= ?catrevE; rel. Qed.

Lemma list_rel_map A (f: A -> R) (g: A -> S):
  (forall a, rel (f a) (g a)) -> forall l, list_rel (map f l) (map g l).
Proof. intro. induction l; simpl; rel. Qed.

Definition pair_rel: R*R -> S*S -> Prop :=
  fun p q => rel p.1 q.1 /\ rel p.2 q.2.

Lemma rpair: forall p q, rel p q -> forall p' q', rel p' q' -> pair_rel (p,p') (q,q').
Proof. by []. Qed.

End r.
Global Hint Constructors list_rel: rel.
Global Hint Resolve list_rel_app list_rel_rev rpair: rel.

Lemma list_rel_map' {A B R S} (rel: A -> B -> Prop) (rel': R -> S -> Prop) (f: A -> R) (g: B -> S):
  (forall a b, rel a b -> rel' (f a) (g b)) ->
  forall h k, list_rel rel h k -> list_rel rel' (map f h) (map g k).
Proof. intros H h k. induction 1; simpl; rel. Qed.


(** derived containment relations in neighborhoods *)
Definition scontains {N: NBH} := (list_rel contains).
Definition pcontains {N: NBH} := (pair_rel contains).


(** ** linear operations *)
Section abs.
 Context {C: Ops0}.

 Definition szer: list C := [].
 
 Fixpoint sadd (P Q: list C): list C :=
   match P,Q with
   | [],C | C,[] => C
   | a::P,b::Q => (a+b)::sadd P Q
   end.
 
 Definition sopp (P: list C): list C := map (sub 0) P.
 
 Definition ssub P Q := sadd P (sopp Q).
 
 Definition sscal a (P: list C): list C := map (mul a) P.

 Definition cons0 (p: list C) := match p with [] => p | _=>0::p end.
 
 Definition cons00 (p: list C) := match p with [] => p | _=>0::0::p end.

 Fixpoint split_list (n: nat) (p: list C) :=
   match n with
   | 0 => ([],p)
   | S n => match p with
             | [] => ([],[])
             | a::q => let (p,p') := split_list n q in (a::p,cons0 p')
             end
   end.

End abs.
Arguments sadd {C} !P !Q / .  

(** ** evaluation and properties of the operations on reals *)
Section e.
 Variable M: nat -> R -> R.

 (** evaluation in the given basis *)
 Fixpoint eval_ n (P: list R) (x: R): R :=
   match P with
   | [] => 0
   | a::Q => a * M n x + eval_ (S n) Q x
   end.
 Definition eval := eval_ 0.

 Lemma eval_zer (x: R): eval szer x = 0.
 Proof. reflexivity. Qed.
 Lemma eval_app_: forall P Q (x: R) n, eval_ n (P ++ Q) x = eval_ n P x + eval_ (length P + n) Q x.
 Proof.
   intros P; induction P as [|a P IH]; intros Q x n.
   - compute; ring.
   - rewrite /=IH/= plus_n_Sm. ring.
 Qed.
 Lemma eval_app: forall P Q (x: R), eval (P ++ Q) x = eval P x + eval_ (length P) Q x.
 Proof. intros; rewrite /eval eval_app_ -plus_n_O //. Qed.
 Lemma eval_add_: forall P Q (x: R) n, eval_ n (sadd P Q) x = eval_ n P x + eval_ n Q x.
 Proof. induction P as [|a P IH]; intros [|b Q] x n; rewrite /=?IH/=; ring. Qed.
 Lemma eval_add: forall P Q (x: R), eval (sadd P Q) x = eval P x + eval Q x.
 Proof. intros. apply eval_add_. Qed.
 Lemma eval_opp_: forall P (x: R) n, eval_ n (sopp P) x = -eval_ n P x.
 Proof. induction P as [|a P IH]; intros x n; rewrite /=?IH/=; ring. Qed.
 Lemma eval_opp: forall P (x: R), eval (sopp P) x = -eval P x.
 Proof. intros. apply eval_opp_. Qed.
 Lemma eval_sub_: forall P Q (x: R) n, eval_ n (ssub P Q) x = eval_ n P x - eval_ n Q x.
 Proof. intros. rewrite /ssub eval_add_ eval_opp_ /=. ring. Qed.
 Lemma eval_sub: forall P Q (x: R), eval (ssub P Q) x = eval P x - eval Q x.
 Proof. intros. apply eval_sub_. Qed.
 Lemma eval_scal_: forall a P (x: R) n, eval_ n (sscal a P) x = a * eval_ n P x.
 Proof. induction P as [|b P IH]; intros; rewrite /=?IH/=; ring. Qed. 
 Lemma eval_scal a P (x: R): eval (sscal a P) x = a * eval P x.
 Proof. intros. apply eval_scal_. Qed. 
 Lemma eval_cons0_ n p (x: R): eval_ n (cons0 p) x = eval_ (S n) p x.
 Proof. destruct p=>//=. ring. Qed.
 Lemma eval_cons00_ n p (x: R): eval_ n (cons00 p) x = eval_ (S (S n)) p x.
 Proof. destruct p=>//=. ring. Qed.
 Lemma eval_split_list n: forall p x, eval p x = eval (split_list n p).1 x + eval (split_list n p).2 x.
 Proof.
   unfold eval. generalize O as m. 
   elim: n => [|n IH] m p x. simpl; lra.
   case: p => [|a p] =>/=. lra.
   rewrite IH. destruct (split_list n p) as [q q'] =>/=.
   rewrite eval_cons0_. lra.
 Qed.

 Hypothesis H: forall n x, continuity_pt (M n) x. 
 Lemma eval_cont_ P x: forall n, continuity_pt (eval_ n P) x.
 Proof.
   elim:P=>[|a Q IH] n /=. 
   + by apply continuity_pt_const. 
   + apply continuity_pt_plus=>//.
     apply continuity_pt_mult=>//.
     by apply continuity_pt_const.
 Qed.

 Lemma eval_cont_basis P x: continuity_pt (eval P) x.
 Proof. apply eval_cont_. Qed.

 Lemma eval_ex_RInt P a b: ex_RInt (eval P) a b.
 Proof.
   apply ex_RInt_Reals_1; case (Rle_dec a b) => Hab; [ | apply RiemannInt.RiemannInt_P1];
   apply RiemannInt.continuity_implies_RiemannInt; try lra;
     now intros t _; apply eval_cont_basis.
 Qed.
End e.


(** ** parametricity of the operations  *)

Section s.
 Context {R S: Ops0}.
 Variable T: Rel0 R S.
 Notation sT := (list_rel T).
 Lemma rsadd: forall x y, sT x y -> forall x' y', sT x' y' -> sT (sadd x x') (sadd y y').
 Proof.
   intros P Q H. induction H. rel. 
   intros P' Q' H'. destruct H'; simpl in *; rel. 
 Qed.
 Lemma rsscal a b: rel T a b -> forall x y, sT x y -> sT (sscal a x) (sscal b y).
 Proof. induction 2; simpl; rel.  Qed.
 Lemma rsopp: forall x y, sT x y -> sT (sopp x) (sopp y).
 Proof. induction 1; simpl; rel. Qed.
 Lemma rssub: forall x y, sT x y -> forall x' y', sT x' y' -> sT (ssub x x') (ssub y y').
 Proof. intros. apply rsadd; auto using rsopp. Qed.
 Lemma rszer: sT szer szer.
 Proof. unfold szer. rel. Qed.
 Lemma rcons0: forall x y, sT x y -> sT (cons0 x) (cons0 y).
 Proof. intros ??[|]=>/=; rel. Qed.
 Lemma rcons00: forall x y, sT x y -> sT (cons00 x) (cons00 y).
 Proof. intros ??[|]=>/=; rel. Qed.
 Hint Resolve rcons0: rel.
 Lemma rsplit_list n: forall p q, sT p q -> pair_rel sT (split_list n p) (split_list n q).
 Proof.
   elim: n=>[|n IH]. simpl. rel.
   destruct 1 as [|x y p q XY PQ]; simpl. rel.
   generalize (IH _ _ PQ). case (split_list n p). case (split_list n q). 
   intros ???? [? ?]. rel.
 Qed.
End s.
Global Hint Resolve rsadd rsscal rsopp rssub rszer rcons0 rcons00: rel.


(** ** Basis: requirements for generating pseudo-polynomial models (in approx.v) *)

Class BasisOps_on (C: Type) := {
  lo: C;
  hi: C;
  beval: list C -> C -> C;
  bmul: list C -> list C -> list C;
  bone: list C;
  bid: list C;
  bprim: list C -> list C;
  (* range is an optional operation (implemented locally if absent, e.g., for Taylor models) *)
  brange: option (list C -> C*C); 
  interpolate: Z -> (C -> C) -> list C;
}.

(** Basis operations immediately give an Ops0 structure on [list C] *)
Canonical Structure listOps0 (C: Ops1) (B: BasisOps_on C) := {|
  car := list C;
  add := sadd;
  mul := bmul;
  sub := ssub;
  zer := szer;
  one := bone|}.

Class BasisOps {N: NBH} := {
  (** concrete operations on intervals & floating points *)
  BI:> BasisOps_on II;
  BF:> BasisOps_on FF;
}.

Definition dom {BO: BasisOps_on R} (x: R) := lo <= x <= hi.
Definition Dom `{BO: BasisOps} (X: II) := is_le lo X && is_le X hi.

Class Basis {N: NBH} (B: BasisOps) := {

  (** the mathematical basis itself *)
  TT: nat -> R -> R;

  (** abstract operations on reals *)
  BR:> BasisOps_on R;

  (** the domain is non-trivial *)
  lohi: lo<hi;
  
  (** properties of BR *)
  evalE: forall p x, beval p x = eval TT p x;
  eval_cont: forall p x, continuity_pt (eval TT p) x;
  eval_mul: forall p q x, eval TT (bmul p q) x = eval TT p x * eval TT q x;
  eval_one: forall x, eval TT bone x = 1;
  eval_id: forall x, eval TT bid x = x;
  eval_prim': forall p a b, is_RInt (eval TT p) a b (eval TT (bprim p) b - eval TT (bprim p) a);
  eval_prim: forall p a b, eval TT (bprim p) b - eval TT (bprim p) a = RInt (eval TT p) a b;
  eval_range: match brange with
               | Some range => (forall p x, dom x -> (range p).1 <= eval TT p x <= (range p).2)
               | None => True end;
  
  (** link between BI and BR *)
  rlo: contains lo lo;
  rhi: contains hi hi;
  rbmul: forall p q, scontains p q ->
         forall p' q', scontains p' q' ->
                         scontains (bmul p p') (bmul q q');
  rbone: scontains bone bone;
  rbid: scontains bid bid;
  rbprim: forall p q, scontains p q ->
                     scontains (bprim p) (bprim q);
  rbeval: forall p q, scontains p q ->
          forall x y, contains x y ->
                      contains (beval p x) (beval q y);
  rbrange: match brange,brange with
           (* TODO: option_rel *)
           | Some rangeI,Some rangeR =>
             (forall p q, scontains p q -> pair_rel contains (rangeI p) (rangeR q))                                            
           | None,None => True
           | _,_ => False
           end;
}.
Global Hint Resolve rbmul rbone rbid rbprim rbeval rlo rhi: rel.


Lemma domlo `{Basis}: dom lo.
Proof. generalize lohi. split; lra. Qed.

Lemma domhi `{Basis}: dom hi.
Proof. generalize lohi. split; lra. Qed.

Lemma DomE `{Basis} X: wreflect (forall x, contains X x -> dom x) (Dom X).
Proof.
  rewrite /Dom.
  case is_leE=>[Lo|]. 2: constructor. 
  case is_leE=>[Hi|]; constructor=> x Xx.
  split; [apply Lo|apply Hi]=>//. apply rlo. apply rhi.
Qed.
