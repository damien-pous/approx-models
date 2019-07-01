(** * Operations on linear combinations (generalised polynomials) *)

From mathcomp Require Import ssrnat.
From mathcomp Require Export seq.
Require Export neighborhood.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** lifting relations to sequences and pairs *)
Section r.
Variables R S: Type.
Variable rel: R -> S -> Prop.
Inductive seq_rel: seq R -> seq S -> Prop :=
| rnil: seq_rel [::] [::]
| rcons: forall x y h k, rel x y -> seq_rel h k -> seq_rel (x::h) (y::k).
Hint Constructors seq_rel: rel.
Lemma seq_rel_app: forall h k, seq_rel h k -> forall p q, seq_rel p q -> seq_rel (h++p) (k++q).
Proof. induction 1; simpl; rel. Qed.
Hint Resolve seq_rel_app: rel.
Lemma seq_rel_rev: forall h k, seq_rel h k -> seq_rel (rev h) (rev k).
Proof. induction 1; rewrite /= /rev /= ?catrevE; rel. Qed.
Lemma seq_rel_map A (f: A -> R) (g: A -> S):
  (forall a, rel (f a) (g a)) -> forall l, seq_rel (map f l) (map g l).
Proof. intro. induction l; simpl; rel. Qed.
Definition pair_rel: R*R -> S*S -> Prop :=
  fun p q => rel p.1 q.1 /\ rel p.2 q.2.
Lemma rpair: forall p q, rel p q -> forall p' q', rel p' q' -> pair_rel (p,p') (q,q').
Proof. by []. Qed.
End r.
Hint Constructors seq_rel: rel.
Hint Resolve seq_rel_app seq_rel_rev rpair: rel.


(** ** linear operations *)
Section abs.
 Context {C: Ops0}.

 Definition szer: seq C := [::].
 
 Fixpoint sadd (P Q: seq C): seq C :=
   match P,Q with
   | [::],C | C,[::] => C
   | a::P,b::Q => (a+b)::sadd P Q
   end.
 
 Definition sopp (P: seq C): seq C := map (sub 0) P.
 
 Definition ssub P Q := sadd P (sopp Q).
 
 Definition sscal a (P: seq C): seq C := map (mul a) P.

 Definition cons0 (p: seq C) := match p with [::] => p | _=>0::p end.
 
 Definition cons00 (p: seq C) := match p with [::] => p | _=>0::0::p end.

 Fixpoint split_seq (n: nat) (p: seq C) :=
   match n with
   | 0 => ([::],p)
   | n.+1 => match p with
             | [::] => ([::],[::])
             | a::q => let (p,p') := split_seq n q in (a::p,cons0 p')
             end
   end.

End abs.
Arguments sadd {C} !P !Q / .  

(** ** evaluation and properties of the operations on reals *)
Section e.
 Variable M: nat -> R -> R.

 (** evaluation in the given basis *)
 Fixpoint eval_ n (P: seq R) (x: R): R :=
   match P with
   | [::] => 0
   | a::Q => a * M n x + eval_ (S n) Q x
   end.
 Definition eval := eval_ 0.

 Lemma eval_zer (x: R): eval szer x = 0.
 Proof. reflexivity. Qed.
 Lemma eval_app_: forall P Q (x: R) n, eval_ n (P ++ Q) x = eval_ n P x + eval_ (size P + n) Q x.
 Proof.
   intros P; induction P as [|a P IH]; intros Q x n.
   - compute; ring.
   - rewrite /=IH/= addnS addSn. ring.
 Qed.
 Lemma eval_app: forall P Q (x: R), eval (P ++ Q) x = eval P x + eval_ (size P) Q x.
 Proof. intros; rewrite /eval eval_app_ addn0 //. Qed.
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
 Lemma eval_cons0_ n p (x: R): eval_ n (cons0 p) x = eval_ n.+1 p x.
 Proof. destruct p=>//=. ring. Qed.
 Lemma eval_cons00_ n p (x: R): eval_ n (cons00 p) x = eval_ n.+2 p x.
 Proof. destruct p=>//=. ring. Qed.
 Lemma eval_split_seq n: forall p x, eval p x = eval (split_seq n p).1 x + eval (split_seq n p).2 x.
 Proof.
   unfold eval. generalize O as m. 
   elim: n => [|n IH] m p x. simpl; lra.
   case: p => [|a p] =>/=. lra.
   rewrite IH. destruct (split_seq n p) as [q q'] =>/=.
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
 Notation sT := (seq_rel T).
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
 Lemma rsplit_seq n: forall p q, sT p q -> pair_rel sT (split_seq n p) (split_seq n q).
 Proof.
   elim: n=>[|n IH]. simpl. rel.
   destruct 1 as [|x y p q XY PQ]; simpl. rel.
   generalize (IH _ _ PQ). case (split_seq n p). case (split_seq n q). 
   intros ???? [? ?]. rel.
 Qed.
End s.
Hint Resolve rsadd rsscal rsopp rssub rszer rcons0 rcons00: rel.


(** ** Basis operations and their validity  *)
                                          
(** elementary ingredients allowing to construct a FunOps based on models *)
Class BasisOps_on (M: nat -> R -> R) (C: Type) :=
  {
    lo: C;
    hi: C;
    beval: seq C -> C -> C;
    bmul: seq C -> seq C -> seq C;
    bone: seq C;
    bid: seq C;
    bprim: seq C -> seq C;
    (* range is an optional operation (implemented locally if absent, e.g., for Taylor models) *)
    brange: option (seq C -> C*C); 
    interpolate: Z -> (C -> C) -> seq C;
  }.
Definition BasisOps T := forall C: Ops1, BasisOps_on T C.

(** extension of the [contains] relation to sequences and pairs  *)
Definition scontains {N: NBH} := (seq_rel contains).
Definition pcontains {N: NBH} := (pair_rel contains).

(** domain of a basis, as a predicate on reals *)
Definition dom T (B: BasisOps_on T R) x := lo <= x <= hi.

(** domain of a basis, as an interval  *)
Definition Dom {N: NBH} T (B: BasisOps_on T II): II := bnd lo hi.

Section vb.
 Context {N: NBH} {T: nat -> R -> R} {B: BasisOps T}.
 Let BR: BasisOps_on T R := B ROps1.
 Let BI: BasisOps_on T II := B II.
 Existing Instances BR BI.
 Notation eval := (eval T).
 Notation dom := (dom BR).
 Class ValidBasisOps :=
   {
     (** properties of BR *)
     lohi: lo < hi;
     evalE: forall p x, beval p x = eval p x;
     eval_cont: forall p x, continuity_pt (eval p) x;
     eval_mul: forall p q x, eval (bmul p q) x = eval p x * eval q x;
     eval_one: forall x, eval bone x = 1;
     eval_id: forall x, eval bid x = x;
     eval_prim': forall p a b, is_RInt (eval p) a b (eval (bprim p) b - eval (bprim p) a);
     eval_prim: forall p a b, eval (bprim p) b - eval (bprim p) a = RInt (eval p) a b;
     eval_range: match brange with
                  | Some range => (forall p x, dom x -> (range p).1 <= eval p x <= (range p).2)
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
              | Some rangeI,Some rangeR =>
                (forall p q, scontains p q -> pair_rel contains (rangeI p) (rangeR q))                                            
              | None,None => True
              | _,_ => False
              end;
   }.
End vb.
Arguments ValidBasisOps _ [_] _. 
Hint Resolve rlo rhi rbmul rbone rbid rbprim rbeval: rel.

(** Basis operations immediately give an Ops0 structure on [seq C] *)
Canonical Structure seqOps0 M (C: Ops1) (B: BasisOps_on M C) :=
  {| car := seq C;
     add := sadd;
     mul := bmul;
     sub := ssub;
     zer := szer;
     one := bone|}.
