(** * Rigorous approximations (models) in a generic basis *)

Require Export vectorspace.
Require Import errors.
Require div sqrt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.  

(** models: polynomials with a remainder *)
Record Model C := { pol: list C; rem: C }.

(** ** operations on rigorous approximations *)
Section n.
 Context {N: NBH} {B: Basis}.
 Notation Model := (Model (car (ops0 (@II N)))).

 (** range of a polynomial *)
 Definition srange p: II :=
   match brange with
   | None => beval p (bnd lo hi)
   | Some range => let (m,M):=range p in bnd m M
   end.

 (** model with empty remainder *)
 Definition msingle p: Model := {| pol := p; rem := 0 |}.

 (** uninformative model  *)
 Definition mbot: Model := {| pol := 0; rem := bot |}.

 (** basic operations on models *)
 Definition madd (M N: Model): Model :=
   {| pol := pol M + pol N;
      rem := rem M + rem N |}.
 Definition msub (M N: Model): Model :=
   {| pol := pol M - pol N ;
      rem := rem M - rem N |}.
 Definition mscal (x: II) (M: Model): Model :=
   {| pol := sscal x (pol M);
      rem := x * rem M |}.
 Definition mmul (M N: Model): Model :=
   {| pol := pol M * pol N;
      rem := srange (pol M) * rem N + srange (pol N) * rem M + rem M * rem N |}.
 Definition mzer: Model := msingle 0.
 Definition mone: Model := msingle 1.

 (** by defining this structure, we get nice notations for the above operations on models *)
 Local Canonical Structure MOps0: Ops0 :=
   {|
     car:=Model;
     add:=madd;
     sub:=msub;
     mul:=mmul;
     zer:=mzer;
     one:=mone;
   |}.

 (** identity *)
 Definition mid: Model := msingle bid.

 (** constant *)
 Definition mcst c: Model := mscal c mone.

 (** integration *)
 Definition mintegrate_unsafe (M: Model) (a b: II): II :=
   let N := bprim (pol M) in 
   beval N b - beval N a + (b-a)*rem M.
 Definition mintegrate (M: Model) (a b: II): E II :=
   if Dom a && Dom b then ret (mintegrate_unsafe M a b) else err "mintegrate: invalid bounds".
 
 (** evaluation, without checking that the argument belongs to the domain *)
 Definition meval_unsafe (M: Model) (x: II): II := beval (pol M) x + rem M.

 (** evaluation *)
 Definition meval (M: Model) (x: II): E II :=
   if Dom x then ret (meval_unsafe M x) else err "meval: argument out of bounds".
 
 (** range *)
 Definition mrange (M: Model): II := srange (pol M) + rem M.

 (** truncation of a model *)
 Definition mtruncate (n: nat) (M: Model): Model :=
   let (p,q) := split_list n (pol M) in 
   {| pol := p; rem := rem M + srange q |}.

 (** division: h' and w' are given by an oracle
    h' ~ f'/g'
    w' ~ 1 /g' *)
 Definition mdiv_aux (f' g' h' w': Model): E Model :=
   let k1' := 1 - w'*g' in
   let k2' := w' * (g' * h' - f') in
   match mag (mrange k1'), mag (mrange k2') with
   | Some mu', Some b' =>
     if is_lt mu' 1 then ret {| pol := pol h';
                            rem := rem h' + sym (b' / (1 - mu')) |}
     else err "mdiv: non contractive operator"
   | _,_ => err "mdiv: error when checking the ranges of k1/k2"
   end.

 (** square root: g' and k' are given by an oracle 
    g' ~ sqrt f'
    k' ~ 1 / 2g' *)
 Definition msqrt_aux (f' h' w': Model) (x0' : II): E Model :=
   (* TODO: move to a plain meval with monadic style *)
   if ~~ Dom x0' then err "msqrt: given point out of the domain" else
   let y0' := meval_unsafe w' x0' in
   if ~~ is_lt 0 y0' then err "msqrt: potentially negative value" else
   let k1' := 1 - (mscal (fromZ 2) (w' * h')) in
   let k2' := w' * (h' * h' - f') in
   match mag (mrange k1'), mag (mrange w'), mag (mrange k2') with
   | Some mu0', Some mu1', Some b' =>
     let delta' := pow 2 (1 - mu0') - fromZ 8 * b' * mu1' in
     if is_lt mu0' 1 then
       if is_lt 0 delta' then
         let rmin' := (1 - mu0' - sqrt delta')/(fromZ 4 * mu1') in
         let mu' := mu0' + fromZ 2 * mu1' * rmin' in
         if is_lt mu' 1 then ret {| pol := pol h'; rem:=rem h' + sym rmin' |}             
         else err "msqrt: missed mu'<1"
       else err "msqrt: missed 0<delta"
     else err "msqrt: missed mu0<1"
   | _,_,_ => err "msqrt: error when checking the ranges of k1/w/k2"
   end.

 (** auxiliary conversion functions to perform interpolation with floating points *)
 Definition mcf (M: Model): list FF := map I2F (pol M).
 Definition mfc (p: list FF): Model := {| pol := map F2I p; rem := 0 |}.

 (** division and square root, using interpolation as oracle *)
 Definition mdiv n (M N: Model): E Model :=
   let p := mcf M in
   let q := mcf N in
   mdiv_aux M N
            (mfc (interpolate n (fun x => beval p x / beval q x)))
            (mfc (interpolate n (fun x => 1 / beval q x))).
 Definition msqrt n (M: Model): E Model :=
   let p := mcf M in
   let h := interpolate n (fun x: FF => sqrt (beval p x)) in
   msqrt_aux M
             (mfc h)
             (mfc (interpolate n (fun x: FF => 1 / (fromZ 2 * beval h x))))
             ((lo+hi)//2).

 (** ** correctness of the above operations in valid bases *)
 Notation eval := (vectorspace.eval TT).
 
 (** containment relation for models *)
 Definition mcontains (M: Model) (f: R -> R) :=
  exists p, scontains (pol M) p /\ forall x, dom x -> contains (rem M) (f x - eval p x).
 
 Lemma mcontains_ext M f g : (forall x, dom x -> f x = g x) -> mcontains M f -> mcontains M g.
 Proof.
   move => Hfg [f0 [Hf0 Hf]].
   exists f0; split => // x Hx.
   rewrite -Hfg; auto.
 Qed.

 (** *** basic operations *)
 
 Lemma rmeval_unsafe (M: Model) f:
   mcontains M f -> forall X x, contains X x -> dom x -> contains (meval_unsafe M X) (f x).
 Proof.
   intros (p&Hp&H) X x Xx HX. rewrite /meval.
   replace (f x) with (eval p x + (f x - eval p x)) by (simpl; ring).
   apply radd; auto. rewrite -evalE. by apply rbeval. 
 Qed.

 Lemma rmeval (M: Model) f:
   mcontains M f -> forall X x, contains X x -> EP' contains (meval M X) (f x).
 Proof.
   intros Mf X x Xx. rewrite /meval.
   case DomE=>// H. constructor.
   now apply rmeval_unsafe; auto. 
 Qed.
 
 Lemma rdom x: dom x -> contains (bnd lo hi) x.
 Proof. rewrite /dom /Dom. apply bndE. apply rlo. apply rhi. Qed.

 Lemma eval_srange P p x: scontains P p -> dom x -> contains (srange P) (eval p x).
 Proof.
   rewrite /srange => Pp Hx.
   generalize (rbrange). generalize (eval_range). unfold BI; simpl.
   case brange=>[rangeR eval_rangeR|_]; case brange=>[rangeI rrange|] =>//.
   - generalize (rrange _ _ Pp).
     generalize (eval_rangeR p _ Hx).
     destruct (rangeI P) as [A C].
     simpl (car (ops0 ROps1)).
     destruct (rangeR p) as [a c] =>/=.
     intros E [Aa Cc]. eapply bndE; eauto.
   - move=>_. rewrite -evalE. apply rbeval=>//. by apply rdom. 
 Qed.   

 Lemma eval_mrange M f : mcontains M f -> forall x, dom x -> contains (mrange M) (f x).
 Proof.
   move => [p [Hp Hf]] x Hx.
   rewrite /mrange; replace (f x) with (eval p x + (f x - eval p x)); last by rewrite /=; ring.
   apply radd; auto. by apply eval_srange. 
 Qed.
 
 Lemma msingle' P p: scontains P p -> mcontains (msingle P) (eval p).
 Proof.
   intros. exists p. split=>// x Hx.
   replace (_-_) with R0 by (simpl; ring).
   apply rzer.
 Qed.
 
 Lemma rmadd: forall M f, mcontains M f -> forall P g, mcontains P g -> mcontains (madd M P) (f+g).
 Proof.
   move=> M f [p [Hp Hf]] P g [q [Hq Hg]]. exists (p+q); split. by apply rsadd.
   move=> x Hx. replace (_-_) with ((f x - eval p x) + (g x - eval q x)).
   apply radd; auto. rewrite eval_add/=/f_bin; ring. 
 Qed.
 
 Lemma rmsub: forall M f, mcontains M f -> forall P g, mcontains P g -> mcontains (msub M P) (f-g).
 Proof.
   move=> M f [p [Hp Hf]] P g [q [Hq Hg]]. exists (p-q); split. by apply rssub.
   move=> x Hx. replace (_-_) with ((f x - eval p x) - (g x - eval q x)).
   apply rsub; auto. rewrite eval_sub/=/f_bin; ring. 
 Qed.
 
 Lemma rmscal: forall C c, contains C c -> forall M f, mcontains M f -> mcontains (mscal C M) (fun x => c * f x). 
 Proof.
   move=> C c Hc M f [p [Hp Hf]]. exists (sscal c p); split. by apply rsscal.
   move=> x Hx. replace (_-_) with (c*(f x - eval p x)).
   apply rmul; auto. rewrite eval_scal/=; ring. 
 Qed.
 
 Lemma rmmul: forall M f, mcontains M f -> forall P g, mcontains P g -> mcontains (mmul M P) (f*g).
 Proof.
   move=> M f [p [Hp Hf]] P g [q [Hq Hg]]. exists (p*q); split. by apply rbmul.
   move=> x Hx.
   replace (_-_) with
       (eval p x * (g x - eval q x) + eval q x * (f x - eval p x) + (f x - eval p x) * (g x - eval q x)) by (rewrite eval_mul/=/f_bin; ring).
   apply radd. apply radd.
   - apply rmul. by apply eval_srange. by apply Hg. 
   - apply rmul. by apply eval_srange. by apply Hf. 
   - apply rmul; auto. 
 Qed.
 
 Lemma rmzer: mcontains mzer 0.
 Proof.
   exists 0; split. apply rszer.
   move=> x Hx. rewrite eval_zer/=/f_cst. replace (_-_) with R0 by (simpl;ring). apply rzer.
 Qed.
 
 Lemma rmone: mcontains mone 1.
 Proof.
   exists 1; split. apply rbone.
   move=> x Hx. rewrite eval_one/=/f_cst. replace (_-_) with R0 by (simpl;ring). apply rzer.
 Qed.
 
 Lemma rmcst C (c : R): contains C c -> mcontains (mcst C) (f_cst c).
 Proof.
   move => Hc; eapply mcontains_ext.
   by move => x Hx; rewrite -[in RHS](Rmult_1_r c).
   apply rmscal => //; apply rmone.
 Qed.
 
 Lemma rmid: mcontains mid ssrfun.id.
 Proof.
   exists bid; split. apply rbid.
   move=> x Hx. rewrite eval_id/=. replace (_-_) with R0 by (simpl;ring). apply rzer.
 Qed.
 
 Lemma rmbot f: mcontains mbot f.
 Proof.
   exists 0; split. apply rszer.
   intros. apply botE.
 Qed.

 Canonical Structure mcontains_Rel0: Rel0 MOps0 (f_Ops0 R ROps0) :=
   {|
     rel := mcontains;
     radd := rmadd;
     rsub := rmsub;
     rmul := rmmul;
     rzer := rmzer;
     rone := rmone;    
   |}.

 Lemma rmtruncate n: forall F f, mcontains F f -> mcontains (mtruncate n F) f.
 Proof.
   intros F f (p&Hp&H). unfold mtruncate.
   generalize (rsplit_list n Hp).
   generalize (eval_split_list TT n p).  
   simpl. case split_list=> p1 p2.
   case split_list=> P1 P2. simpl. 
   intros E [R1 R2]. exists p1. split=>//. 
   intros x Hx.  
   replace (_-_) with ((f x - eval p x) + eval p2 x) by (rewrite E; simpl; ring).
   apply radd. by apply H. by apply eval_srange.
 Qed.

 (** *** integration *)

 Lemma RInt_min a d u f:
   a<d -> (forall x, a<=x<=d -> u <= f x) -> ex_RInt f a d ->
   u <= RInt f a d / (d-a).
 Proof.
   intros ad Hu Hf. apply Rle_div_r. lra.
   transitivity (RInt (fun _ => u) a d).
   rewrite RInt_const Rmult_comm. apply Rle_refl. 
   apply RInt_le=>//. lra. apply ex_RInt_const.
   intros. apply Hu. lra.
 Qed.

 Lemma RInt_max a d v f:
   a<d -> (forall x, a<=x<=d -> f x <= v) -> ex_RInt f a d ->
   RInt f a d / (d-a) <= v.
 Proof.
   intros ad Hv Hf. apply Rle_div_l. lra.
   transitivity (RInt (fun _ => v) a d).
   apply RInt_le=>//. lra. apply ex_RInt_const.
   intros. apply Hv. lra.
   rewrite RInt_const Rmult_comm. apply Rle_refl. 
 Qed.   

 Lemma cont_ex_RInt a d f: dom a -> dom d -> (forall x, dom x -> continuity_pt f x) -> ex_RInt f a d.
 Proof.
   rewrite /dom=> A D H.
   apply ex_RInt_Reals_1; case: (Rle_dec a d) => Hab; [ | apply RiemannInt.RiemannInt_P1];
     apply RiemannInt.continuity_implies_RiemannInt=>//; try lra; move => t Ht; apply H; lra.
 Qed.   
 
 Lemma rmintegrate_unsafe: forall M f, 
     mcontains M f -> (forall x, dom x -> continuity_pt f x) ->
     forall A a, contains A a -> dom a ->
     forall D d, contains D d -> dom d -> contains (mintegrate_unsafe M A D) (RInt f a d).
 Proof.
   move => M f [p [Hp Hf]] Hfcont A a Ha HA D d Hd HD; rewrite /mintegrate.
   have Hfint : ex_RInt f a d by apply cont_ex_RInt. 
   have Hpint : ex_RInt (eval p) a d by apply cont_ex_RInt; last (intros; apply eval_cont).
   have Hfpint : ex_RInt (f - eval p) a d by apply @ex_RInt_minus with (V:=R_NormedModule).
   rewrite (RInt_ext _ (eval p+(f-eval p))); last by (move => x _; rewrite /=/f_bin; lra).
   rewrite RInt_plus => //; first apply radd.
   rewrite -eval_prim -2!evalE. apply rsub; (apply rbeval; [apply rbprim|]); rel. 
   case (Req_dec a d) => ad.
   destruct ad. replace (RInt _ _ _) with (RInt (fun _ => f a - eval p a) a a).
     by rewrite RInt_const; apply rmul; rel.
     apply RInt_ext. intro. unfold Rmin, Rmax. lra.
   replace (RInt _ _ _) with ((d-a) * (RInt (f-eval p) a d / (d-a))) by (simpl; field; lra).
   apply rmul. rel.   
   clear - ad HA HD Hfpint Hf.
   wlog: a d ad HA HD Hfpint / a < d.
   destruct (total_order_T a d) as [[ad'|ad']|ad'] => H.
   - apply H=>//.
   - congruence. 
   - rewrite -opp_RInt_swap; last by apply ex_RInt_swap.
     replace (_/_) with ((RInt (f-eval p) d a / (a-d))) by (rewrite /opp/=; field; lra).
     apply H=>//. congruence. by apply ex_RInt_swap.
   move=>{ad}=>ad. 
   
   case (minE (rem M)) => [U u Uu rMu|] Hu.
   have Hu': forall x, dom x -> u <= f x - eval p x. by intros; apply Rge_le, Hu, Hf.
   have Hu'': u <= RInt (f-eval p) a d / (d-a).
     apply RInt_min=>//. intros. apply Hu'. unfold dom in * ; lra. 
   case (maxE (rem M)) => [V v Vv rMv|] Hv.
   have Hv': forall x, dom x -> f x - eval p x <= v. by intros; apply Hv, Hf.
   have Hv'': RInt (f-eval p) a d / (d-a) <= v.
     apply RInt_max=>//. intros. apply Hv'. unfold dom in * ; lra. 
   apply convex with u v =>//. 
   eapply Hv. apply rMu. apply Hu''.
   case (maxE (rem M)) => [V v Vv rMv|] Hv.
   have Hv': forall x, dom x -> f x - eval p x <= v. by intros; apply Hv, Hf.
   have Hv'': RInt (f-eval p) a d / (d-a) <= v.
     apply RInt_max=>//. intros. apply Hv'. unfold dom in * ; lra. 
   eapply Hu. apply rMv. apply Rle_ge, Hv''.
   specialize (Hf _ HA).
   case (Rle_lt_dec (RInt (f-eval p) a d/(d-a)) (f a-eval p a))=>E.  
   eapply Hu. apply Hf. by apply Rle_ge. 
   eapply Hv. apply Hf. by apply Rlt_le. 
 Qed.

 Lemma rmintegrate: forall M f, 
     mcontains M f -> (forall x, dom x -> continuity_pt f x) ->
     forall A a, contains A a -> 
     forall D d, contains D d -> EP' contains (mintegrate M A D) (RInt f a d).
 Proof.
   intros. rewrite /mintegrate.
   case DomE=>//= Da. 
   case DomE=>//= Db. 
   constructor. now apply rmintegrate_unsafe; auto.
 Qed.
 
 (** *** division *)
 
 Lemma rmdiv_aux (f' g' h' w': Model) f g h w:
   mcontains f' f -> mcontains g' g -> mcontains h' h -> mcontains w' w ->
   EP' mcontains (mdiv_aux f' g' h' w') (f_bin Rdiv f g).
 Proof.
   move => Hf Hg Hh Hw. rewrite /mdiv_aux.
   case magE => [Mu mu MU Hm|]=>//. 
   case magE => [b c bc Hc|]=>//.
   case is_ltE => [Hmu|]=>//.
   specialize (Hmu _ 1 MU (rone _)). 
   destruct (ssrfun.id Hh) as [p [Hp Hh']].
   constructor. exists p; split=>//=.
   move => x Hx. rewrite /f_bin.
   replace (_-_) with ((h x - eval p x) + -(h x - f x / g x)); last by rewrite /=; ring.
   apply radd. by apply Hh'.
   apply symE with (c / (1 - mu)) => /=; last by rel. 
   rewrite Rabs_Ropp.
   refine (div.newton _ _ _ _ Hx) => //.
   + move => t Ht; apply Hm.
     apply eval_mrange with (f := 1-w*g) =>//.
     by apply rmsub; [apply rmone|apply rmmul].
   + move => t Ht; apply Hc. 
     apply eval_mrange with (f := w*(g*h-f)) =>//.
     by apply rmmul; last (apply rmsub; first apply rmmul).
   + lapply (fun H => Hm _ (eval_mrange (f:=1-w*g) H Hx)).
     move => H; split =>//. rewrite <-H. apply Rabs_pos.
     apply rmsub. apply rmone. by apply rmmul.
   + lapply (fun H => Hc _ (eval_mrange (f:=w*(g*h-f)) H Hx)).
     intros <-. apply Rabs_pos.
     apply rmmul=>//. apply rmsub=>//. by apply rmmul.
 Qed.

 Lemma rmdiv n:
   forall M f, mcontains M f ->
   forall N g, mcontains N g -> EP' mcontains (mdiv n M N) (f_bin Rdiv f g).
 Proof.
   move => M f Mf P g Pg. eapply rmdiv_aux=>//; 
   apply msingle', list_rel_map, F2IE.
 Qed.

 (** *** square root *)
 
 Lemma rmsqrt_aux (f' h' w': Model) (x0' : II) (f h w : R -> R) x0:
   mcontains f' f -> mcontains h' h -> mcontains w' w ->
   contains x0' x0 -> 
   (forall x, dom x -> continuity_pt w x) ->
   EP' mcontains (msqrt_aux f' h' w' x0') (fun x => R_sqrt.sqrt (f x)).
 Proof.
   move => Hf Hh Hw X0 Hwcont. rewrite /msqrt_aux.
   case DomE=>[Vx0|//=]. specialize (Vx0 _ X0).
   case is_ltE => [Hwx0|]=>[|//=]. 
   specialize (Hwx0 _ _ (rzer _) (rmeval_unsafe Hw X0 Vx0)).
   simpl negb.
   case magE => [Mu0 mu0 MU0 Hmu0|]=>[|//=]. 
   case magE => [Mu1 mu1 MU1 Hmu1|]=>[|//=].
   case magE => [BB b Bb Hb|]=>[|//=].
   case is_ltE =>// Hmu01. specialize (Hmu01 _ _ MU0 (rone _)).
   case is_ltE =>// Hmu0b. 
   destruct (ssrfun.id Hh) as [p [Hp Hh']].
   case is_ltE => [Hmu|] =>//. 
   constructor. exists p; split =>// x Hx.
   replace (_-_) with ((h x - eval p x) + -(h x - R_sqrt.sqrt (f x))); last by rewrite /=; ring.
   apply radd; first by apply Hh'.
   set rmin := sqrt.rmin b mu0 mu1.
   eapply symE with rmin; first last.
    apply rdiv. apply rsub. apply rsub=>//. apply rone. apply rsqrt.
    apply rsub. rewrite Rpow. apply rpow. apply rsub=>//. apply rone. rel. rel. 
   rewrite Rabs_Ropp.
   lapply (fun H x Hx => Hmu0 _ (eval_mrange (x:=x) (f:=fun x => 1 - 2 * (w x*h x)) H Hx)); last first.
    apply rmsub. apply rmone. apply rmscal. apply rfromZ. by apply rmmul.
    intro Hmu0'. 
   pose proof (fun x Hx => Hmu1 _ (eval_mrange (x:=x) Hw Hx))as Hmu1'.
   lapply (fun H x Hx => Hb _ (eval_mrange (x:=x) (f:=w*(h*h-f)) H Hx));
     last by apply rmmul => //; apply rmsub => //; apply rmmul.
   intro Hb'. 
   (unshelve eapply (sqrt.newton (w:=w) _ _ _ _ _ _ _ _ _ _ _ Hx)) =>//.
   + by move => t Ht; rewrite Rmult_assoc; auto. 
   + by move => t Ht /=; rewrite Rmult_1_r; apply Hb'.     
   + split=>//. rewrite <- (Hmu0' _ Hx). apply Rabs_pos. 
   + apply Rlt_le_trans with (Rabs (w x0)); eauto. clear -Hwx0. split_Rabs; simpl in *; lra.
   + specialize (Hb' _ Hx). by rewrite <-Rabs_pos in Hb'. 
   + apply Rlt_le, Hmu0b. apply rzer. apply rsub. rewrite Rpow. apply rpow, rsub =>//. apply rone. rel.
   + apply Hmu; last apply rone.
     apply radd => //. apply rmul. rel. apply rdiv; last rel. apply rsub. 
     apply rsub. apply rone. rel. apply rsqrt. apply rsub.
     rewrite /=. apply rmul. apply rsub. apply rone. rel. apply rmul. apply rsub. apply rone. rel. apply rone.
     apply rmul; first apply rmul; rel. 
   + unfold dom. clear. intros; simpl in *; lra. 
   + exists x0; auto.
 Qed.

 Lemma rmsqrt n M f: 
   mcontains M f -> EP' mcontains (msqrt n M) (f_unr R_sqrt.sqrt f).
 Proof.
   move => Mf. eapply rmsqrt_aux with _ _ ((lo+hi)//2) => //;
    try apply msingle', list_rel_map, F2IE. rel. 
   move => ??. apply eval_cont.
 Qed.


 (** packing all operations together *)
 Definition model: FunOps :=
  {|
    MM:=MOps0;
    interfaces.mid:=mid;
    interfaces.mcst:=mcst;
    interfaces.meval:=meval;
    interfaces.mintegrate:=mintegrate;
    interfaces.mdiv:=mdiv;
    interfaces.msqrt:=msqrt;
    interfaces.mtruncate:=mtruncate;
    interfaces.mrange:=mrange;
    interfaces.mdom := dom;
    interfaces.mcontains := mcontains_Rel0;
    interfaces.rmid := rmid;
    interfaces.rmcst := rmcst;
    interfaces.rmeval := rmeval;
    interfaces.rmintegrate := rmintegrate;
    interfaces.rmdiv := rmdiv;
    interfaces.rmsqrt := rmsqrt;
    interfaces.rmtruncate := rmtruncate;
    interfaces.rmrange := eval_mrange;               
  |}.

End n.
Arguments model {_} _.
