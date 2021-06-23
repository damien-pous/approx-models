(** * Definition of general polynomial functional operators on Models (monomial basis) 
    to encode polynomial functional equations 
 *)

Require Import Coquelicot.Coquelicot.
Require Import posreal_complements cball domfct banach.
Require Import vectorspace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* Definition of operations on polynomial functional operators *)
Section From_N.
  Context {M : Ops0}.

  (* This function is not efficient, it will be changed *) 
  Fixpoint fromN n : M :=
    match n with
    | 0 => 0
    | S n => 1 + (fromN n)
    end.
  
End From_N.

Section P_Op.
 Context {M: Ops0}.
 Notation poly_op := (list M).
 
 Definition opone: poly_op := [1].
 
 Definition opcst h: poly_op := [h].
  
 (** multiplication *)
 Fixpoint opmul (P Q: poly_op): poly_op :=
   match P with
   | [] => []
   | h::P => sadd (sscal h Q) (0::opmul P Q)
   end.

 (** identity (X) *)
 Definition opid: poly_op := [0;1].
 
 (** composition *)
 Fixpoint opcomp (P Q: poly_op): poly_op :=
   match P with
   | [] => []
   | h::P => sadd (opcst h) (opmul (opcomp P Q) Q)
   end.

 (** derivation on poly_opnoms (equals to the differential of the operator) *)
 Fixpoint opderive_ n (P : poly_op) : poly_op :=
   match P with
   | [] => []
   | h::Q => (mul (fromN n) h)::(opderive_ (n .+1) Q)
   end.

 Definition opderive P : poly_op :=
   match P with
   | [] => []
   | h0::Q => opderive_ 1 Q
   end.

 (** linear time evaluation (Hörner) *)
 Fixpoint opeval (P:list M) (s: M) : M :=
   match P with
   | [] => 0
   | h::Q => add h (mul s (opeval Q s))
   end.

 Definition opnewton (P : list M) (A : M) := ssub opid (sscal A P).

End P_Op.

Section e.
 Context { A : Type } { C : Ops0 }.
 Notation Fun := (A -> C).
 
 (* eval the functional coefficients of P in t *)
 Definition partial_eval (P : list Fun) (t:A) : list C :=
   List.map (fun h => h t) P.

End e.

Lemma opeval_partial_eval (P : list (R -> R)) s (t :R) :
  opeval P s t = opeval (partial_eval P t) (s t).
Proof. elim: P => [ // | h P IHP /=];rewrite /f_bin IHP. lra. Qed. 

(* Compatibility of opeval and partial_eval with sum, sub, scal ... operations
   Think about the modularity of these results *)
Lemma opeval_opp_R (P : list R) s :
  opeval (sopp P) s = - opeval P s.
Proof. elim : P => [ | a p IHP ] /=; try rewrite IHP; lra. Qed. 
 
Lemma opeval_add_R (P Q: list R) s  :
  opeval (sadd P Q) s =  (opeval P s) + (opeval Q s).
Proof.
  move : Q; elim : P => [ Q /= | a p IHP [ | b Q ] /= ]; rewrite /sadd; try rewrite IHP /= ; lra.
Qed.

Lemma opeval_sub_R (P Q: list R) s  :
  opeval (ssub P Q) s  = opeval P s  - opeval Q s.
Proof. rewrite /ssub opeval_add_R opeval_opp_R /=; lra. Qed.

Lemma opeval_scal_R (P : list R) A s  :
  opeval (sscal A P) s = A * opeval P s.
Proof. elim : P => [ | a P IHP ] /=; try rewrite  IHP /=; lra. Qed.

Lemma opeval_opid_R (s: R) : opeval opid s = s.
Proof.  rewrite /opid /=; lra. Qed.

Lemma opeval_opp_RinR (P : list (R -> R)) s (t :R) :
  opeval (sopp P) s t = - opeval P s t.
Proof.
  elim : P => [ | a p IHP ] /=.
  + rewrite /f_cst; lra.
  + rewrite /f_bin /f_cst IHP; lra.
Qed.
    
Lemma opeval_add_RinR (P Q: list (R -> R)) s (t :R) :
  opeval (sadd P Q) s t =  (opeval P s t) + (opeval Q s t).
Proof.
  move : Q; elim : P => [ Q /= | a p IHP [ | b Q ] /= ].
  + rewrite /sadd /f_cst; lra.
  + rewrite /f_bin /sadd /f_cst. lra.
  + rewrite /f_bin IHP /=. lra.
Qed.

Lemma opeval_sub_RinR (P Q: list (R -> R)) s (t :R) :
  opeval (ssub P Q) s t = opeval P s t - opeval Q s t.
Proof. unfold ssub. rewrite opeval_add_RinR opeval_opp_RinR /=. lra. Qed.

Lemma opeval_scal_RinR (P : list (R -> R)) A s (t :R) :
  opeval (sscal A P) s t = A t * opeval P s t.
Proof.
  elim : P => [ | a P IHP ] /=.
  + rewrite /f_cst. lra.
  + rewrite /f_bin IHP /=. lra.
Qed.

Lemma opeval_opid_RinR (s: R->R) (t:R) : opeval opid s t = s t.
Proof.
  rewrite /opid /= /f_bin /f_cst. lra.
Qed.

Lemma partial_eval_opp (P : list (R -> R)) (t:R) :
  partial_eval (sopp P) t = sopp (partial_eval P t).
Proof.
  elim : P => [ //= | a P IHP /=]. by rewrite /f_bin /f_cst IHP.
Qed. 

Lemma partial_eval_add (P Q: list (R -> R)) (t :R) :
  partial_eval (sadd P Q) t = sadd (partial_eval P t) (partial_eval Q t).
Proof.
  move : Q; elim : P => [ Q // | a p IHP [ // | b Q ] /= ]; by rewrite /f_bin IHP.
Qed.

Lemma partial_eval_sub (P Q: list (R -> R)) (t :R) :
  partial_eval (ssub P Q) t = ssub (partial_eval P t) (partial_eval Q t).
Proof. by rewrite /ssub partial_eval_add partial_eval_opp /=. Qed.

Lemma partial_eval_scal (P : list (R -> R)) A  (t :R) :
  partial_eval (sscal A P) t = sscal (A t) (partial_eval P t).
Proof.
  elim : P => [ | a P IHP /= ] //; by rewrite /f_bin IHP. 
Qed.

Lemma partial_eval_opid (t: R) :
  partial_eval (@opid (f_Ops0 R ROps0 )) t = opid.
Proof. by rewrite /opid /= /f_cst. Qed.

(* Results on derivation *)
Lemma ex_derive_opeval (P : list (R->R)) u t : ex_derive (opeval (partial_eval P t)) (u).
Proof. elim: P => [ | a P IHP] /=.
       + apply ex_derive_const.
       + apply @ex_derive_plus. apply ex_derive_const.
         apply ex_derive_mult. apply ex_derive_id. apply IHP.
Qed.

Lemma opderive_succ k ( P : list (R->R))  t x:
  opeval (partial_eval (opderive_ k .+1 P) t) x =  opeval (partial_eval P t) x +  opeval (partial_eval (opderive_ k P) t) x.
Proof. move : k;elim : P => [ | a p IHP ] k /=; try rewrite /f_bin /f_cst IHP /=; lra. Qed.

Lemma opderive0 ( P : list (R->R)) t x:
  opeval (partial_eval (opderive_ 0 P) t) x =  x *  opeval (partial_eval (opderive P) t) x.
Proof. move : P => [ | a P ] /=; rewrite /f_bin /f_cst; lra. Qed.  

Lemma opderive_partial_eval ( P : list (R->R)) t x:
 Derive (opeval (partial_eval P t)) x = opeval (partial_eval (opderive P) t) x.
Proof.
  elim : P => [ | a p IHP ] /=.
  + by rewrite /f_cst Derive_const.
  + rewrite Derive_plus. rewrite Derive_const Derive_mult.
    rewrite IHP Derive_id opderive_succ opderive0 /=; lra.
    apply ex_derive_id. apply ex_derive_opeval. apply ex_derive_const.
    apply ex_derive_mult.  apply ex_derive_id. apply ex_derive_opeval.
Qed.

Lemma eval_is_derive (P : list (R->R)) t (x:R):
  is_derive (opeval (partial_eval P t)) x (opeval (partial_eval (opderive P) t) x).
Proof.
  move : (opderive_partial_eval P t x) => HDe; rewrite -HDe.
  apply Derive_correct. apply ex_derive_opeval.
Qed.  

(* Continuity result *)
Lemma eval_continuity (P : list (R->R)) t (x:R):
  continuity_pt (opeval (partial_eval P t)) x.
Proof. elim: P => [ | a P IHP] /=.  
       Search continuity_pt.
       + apply continuity_pt_const. by rewrite /constant.
       + apply continuity_pt_plus. apply continuity_pt_const. by rewrite /constant.
         apply continuity_pt_mult. apply continuity_pt_id. apply IHP.
Qed.

Section TubePolyn.
Variable (I : R -> Prop).
Notation "{R,I -> R}" := (@domfct_CompleteSpace R_CompleteSpace R_CompleteSpace I).


Lemma Requation1 (x y : R) : x = x - y -> y = 0. 
Proof. simpl. lra. Qed.

Lemma Requation2 (x y : R) : x <> 0 -> x*y = 0 -> y = 0.
Proof.
  intros. Check Rmult_eq_compat_l.
  apply (Rmult_eq_compat_l (/ x) (x*y) 0) in H0. move : H0.
  rewrite -Rmult_assoc Rmult_0_r Rinv_l /= => //. lra.
Qed.

Lemma Rle_sum (a b c d: R) : a <= c -> b <= d -> a + b <= c + d.
Proof. lra. Qed.


Lemma Rinterval_convex (a b u : R) :
  a <= u <= b -> exists eta,  0 <= eta <= 1 /\ u = a + eta * ( b - a).
Proof.
  intros [Hle Hge]. exists ((u-a)/(b-a)); case (Req_dec a b) => Hab.
  + move : Hle Hge; rewrite Hab => Hle Hge; apply Rle_antisym in Hle => //.
    split; rewrite Hle /=; lra.
    have Hbgta : a < b. apply (Rle_trans a u b) in Hle; inversion Hle; by [].
    split; simpl. split.
  + apply Rdiv_le_0_compat; lra. 
  + apply (Rdiv_le_1 (u-a) (b-a)); lra.
  + field; lra.
Qed.

Lemma ball_convex (v s1 s2 : R->R) r eta:
  0 <= eta <= 1 ->
  (forall t, I t -> Rabs ( v t - s1 t ) <= r) ->  (forall t, I t -> Rabs ( v t - s2 t ) <= r) ->
   ( forall t , I t -> Rabs ( v t - ( Rmin (s1 t) (s2 t) + eta * ( Rmax (s1 t) (s2 t) - Rmin (s1 t) (s2 t)))) <= r).
Proof.
  intros [Heta_le Heta_ge] Hs1 Hs2 t It.
  replace ( _ - ( _ + _)) with ( (1-eta)*(v t - Rmin (s1 t) (s2 t)) + eta * ( v t - Rmax (s1 t) (s2 t))). 2: simpl; lra.
  have H1meta : 0 <= 1 - eta. lra.
  eapply Rle_trans. apply Rabs_triang. rewrite !Rabs_mult.
  replace r with ((1-eta)*r + eta * r). 2: simpl;lra.
  apply Rle_sum; rewrite /Rmin /Rmax; destruct (Rle_dec (s1 t) (s2 t)); rewrite Rabs_pos_eq => //; apply Rmult_le_compat_l => //; try apply Hs1 => //; try apply Hs2 => //.
Qed.
  

Lemma newton (F : list (R -> R)) (phi A : R -> R) ( d r lambda : R) :
  (forall (s : R->R), (forall t , I t -> Rabs ( phi t - s t ) <= r ) ->
                      (forall t, I t -> Rabs (  opeval (opderive (opnewton F A)) s t ) <= lambda )) ->
  (forall t, I t ->  Rabs ( A t * opeval F phi t ) <= d) ->
  0 <= lambda /\ lambda < 1 -> 0 <= d /\ 0 <= r -> d + lambda * r <= r ->
  (exists (f: R -> R) , forall t, I t  ->  opeval F f t = 0 /\ Rabs ( f t - phi t ) <= d / (1 - lambda)).
Proof.
  move => Hlambda Hd [ Hl0 Hl1 ] [Hd0 Hr0] Hdlr.
  set lambda0 := mknonnegreal Hl0.
  set d0 := mknonnegreal Hd0.
  (*set r0 := mknonnegreal Hr0.*)
  have Hbound : 0 <= d / (1 - lambda). apply Rle_div_r; lra. 
  set b0 := mknonnegreal Hbound.
  set SB := mkSBall (phi : {R,I -> R}) d0 b0.
  set N : {R,I -> R} -> {R,I -> R} := fun s t => opeval (opnewton F A) s t.
  have Hdlr' : d / (1 - lambda) <= r. apply Rle_div_l; lra. 
  have SBP : SBallProp N lambda0 SB.
   apply mkSBallProp.
  + move => s1 s2 r' SBs1 SBs2 Hs1s2.

    have Hphis1 : forall t, I t -> Rabs ( phi t - s1 t ) <= r.
    apply R_dcballE, cball_sym; move : SBs1 ; rewrite /SBall_pred  /=; apply cball_le => //.
    have Hphis2 : forall t, I t -> Rabs ( phi t - s2 t ) <= r.
    apply R_dcballE, cball_sym; move : SBs2 ; rewrite /SBall_pred  /=; apply cball_le => //.

    apply R_dcballE => t It. rewrite /N. rewrite 2!opeval_partial_eval. 
    move : (MVT_gen (opeval (partial_eval (opnewton F A) t)) (s1 t) (s2 t) (opeval (partial_eval (opderive (opnewton F A)) t))) =>  [ x Ineq  | x Ineq  | u [ Ineq Hmv ] ]. 
    - apply eval_is_derive.
    - apply eval_continuity.
    - rewrite Hmv.
      
      move : (Rinterval_convex Ineq) => [eta] [Heta Hu]. rewrite Hu.
      move : (@ball_convex phi s1 s2 r eta Heta Hphis1 Hphis2) => Hconvex.
      
      move: (Hlambda (fun t=> (Rmin (s1 t) (s2 t) + eta * (Rmax (s1 t) (s2 t) - Rmin (s1 t) (s2 t)))) Hconvex t It) => Hlambda'.
      rewrite Rabs_mult /=. apply Rmult_le_compat. apply Rabs_pos. apply Rabs_pos. 
      by move : Hlambda'; rewrite opeval_partial_eval.
      by move : It; apply R_dcballE.      
      
  + apply cball_sym, R_dcballE => t It /=.
    replace ( _ - _ ) with (A t * opeval F phi t). auto.
    rewrite /N /opnewton opeval_sub_RinR opeval_scal_RinR /= /f_bin /f_cst. lra. 
  + simpl. replace ( _ + _ ) with ( d / (1 - lambda)) => /=. apply Rle_refl.
    field. lra. 

  have HA t : I t -> A t <> 0.
    have Ht0 : forall t0 : R , I t0 -> Rabs (phi t0 - phi t0) <= r.
      move => t0 IT0; by rewrite Rminus_eq_0 Rabs_R0.  
    move => It HAt; move : (Hlambda phi Ht0 t It).
    rewrite /opnewton opeval_partial_eval -opderive_partial_eval.
    rewrite partial_eval_sub partial_eval_scal partial_eval_opid.
    rewrite (Derive_ext _ (fun x => x - (A t) * opeval (partial_eval F t) x)).
    rewrite Derive_minus. rewrite Derive_mult. rewrite Derive_id Derive_const HAt.
    replace ( 1 - _ ) with 1%R => /=. rewrite Rabs_pos_eq => //=.  lra. lra.
    apply ex_derive_const. apply ex_derive_opeval. apply ex_derive_id.
    apply ex_derive_mult. apply ex_derive_const. apply ex_derive_opeval.
    move => x; by rewrite opeval_sub_R opeval_opid_R opeval_scal_R.  
    
  move: (BF_lim_is_fixpoint (Hl1 : lambda0 < 1)  SBP) (BF_lim_inside_sball (Hl1 : lambda0 < 1) SBP).

  set bf := lim (banach.BF N lambda0 SB). rewrite /SBall_pred /=.   
  move => /Rdomfct_close Hbanach_fix /R_dcballE Hbanach_bound; rewrite /N in Hbanach_fix.
  exists bf; split.

  + move : (Hbanach_fix t). rewrite /opnewton.
    rewrite opeval_sub_RinR opeval_scal_RinR opeval_opid_RinR /=.  
    intro Hb; apply Requation1 in Hb => //. apply HA in H. move : H Hb. apply Requation2. 
    
  + by apply Hbanach_bound.
Qed. 

End TubePolyn.
