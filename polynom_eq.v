(** * Definition of general polynomial functional operators on Models (monomial basis) 
    to encode polynomial functional equations 
 *)

Require Import Coquelicot.Coquelicot.
Require Import posreal_complements cball domfct banach.
Require Import vectorspace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition M k x := x^k.

(** naive evaluation (defined in vectorspace) *)
Notation eval_ := (eval_ M).
Notation eval := (eval M).

(* Definition of operations on polynomial functional operators *)
Section From_N.
  Context {M : Ops0}.

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
 
 Fixpoint Xk (k: nat): poly_op :=
   match k with
   | O => [1]
   | S k => 0::Xk k
   end.
  
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

 Definition direct_eval (P :list Fun) (s : Fun) (t:A) : C :=
   opeval (List.map (fun h => h t) P) (s t).

End e.

Lemma direct_eval_cons (P : list (R->R)) (a s : R->R) (t:R) :
  direct_eval (a::P) s t = a t + s t * direct_eval P s t.
Proof. by []. Qed.

Lemma opeval_direct_eval (P : list (R -> R)) s (t :R) : (opeval P s) t = direct_eval P s t.
Proof.
  elim: P => [ // | h P IHP]. 
    by rewrite direct_eval_cons -IHP.
Qed.

Lemma opeval_opp (P : list (R -> R)) s (t :R) :
  opeval (sopp P) s t = - opeval P s t.
Proof.
  elim : P => [ //= | a P IHP /=]. rewrite /f_cst. ring.
  rewrite /f_cst /f_bin IHP. ring.
Qed.  

Lemma opeval_add (P Q: list (R -> R)) s (t :R) :
  opeval (sadd P Q) s t = opeval P s t + opeval Q s t.
Proof.
  move : Q; elim : P => [ Q /= | a p IHP [ | b Q ] /= ].
  + rewrite /sadd /f_cst; lra.
  + rewrite /f_bin /sadd /f_cst. lra.
  + rewrite /f_bin IHP /=. lra.
Qed.

Lemma opeval_sub (P Q: list (R -> R)) s (t :R) :
  opeval (ssub P Q) s t = opeval P s t - opeval Q s t.
Proof. unfold ssub. rewrite opeval_add opeval_opp /=. lra. Qed.

Lemma opeval_scal (P : list (R -> R)) A s (t :R) :
  opeval (sscal A P) s t = A t * opeval P s t.
Proof.
  elim : P => [ | a P IHP ] /=.
  + rewrite /f_cst. lra.
  + rewrite /f_bin IHP /=. lra.
Qed.

Lemma opeval_opid (s: R->R) (t:R) : opeval opid s t = s t.
Proof.
  rewrite /opid /= /f_bin /f_cst. lra.
Qed.

(*Lemma opderive_opp_ n (P : list (R -> R)) :
  opderive_ n (sopp P) = sopp (opderive_ n P) t.
Proof.
  move: n. elim : P => [ //= | a P IHP n /=]. rewrite /f_bin IHP. ring.
  rewrite /f_cst /f_bin IHP. ring.
Qed.  

Lemma opeval_add (P Q: list (R -> R)) s (t :R) :
  opeval (sadd P Q) s t = opeval P s t + opeval Q s t.
Proof.
  move : Q; elim : P => [ Q /= | a p IHP [ | b Q ] /= ].
  + rewrite /sadd /f_cst; lra.
  + rewrite /f_bin /sadd /f_cst. lra.
  + rewrite /f_bin IHP /=. lra.
Qed.

Lemma opeval_sub (P Q: list (R -> R)) s (t :R) :
  opeval (ssub P Q) s t = opeval P s t - opeval Q s t.
Proof. unfold ssub. rewrite opeval_add opeval_opp /=. lra. Qed.

Lemma opeval_scal (P : list (R -> R)) A s (t :R) :
  opeval (sscal A P) s t = A t * opeval P s t.
Proof.
  elim : P => [ | a P IHP ] /=.
  + rewrite /f_cst. lra.
  + rewrite /f_bin IHP /=. lra.
Qed.

Lemma opeval_opid (s: R->R) (t:R) : opeval opid s t = s t.
Proof.
  rewrite /opid /= /f_bin /f_cst. lra.
Qed. 
 *)

(*Lemma opderive_opeval (P : list (R -> R)) s t : opeval (opderive P) s t = Derive (fun x => opeval P s x) t.
Proof.
  move : P => [ /= | h P].
  + by rewrite /f_cst Derive_const.
  + rewrite /= /f_bin.
 *)
(*
Lemma opderive_opnewton (P: list (R -> R)) (A : R->R) s t : opeval (opderive (opnewton P A)) s t = 1 - A t * opeval (opderive P) s t.
Proof.
  rewrite /opnewton. e_sub.
 *)

Section TubePolyn.
Variable (I : R -> Prop).
Notation "{R,I -> R}" := (@domfct_CompleteSpace R_CompleteSpace R_CompleteSpace I).



(*
Lemma newton ( F : list (R -> R)) (phi A : R -> R) (d lambda0 lambda1 r eta : R) :
  let lambda := lambda0 + eta*lambda1 in
  (forall t, D t -> Rabs (1 - A t * opeval (opderive F) phi t) <= lambda0 ) ->
  (forall t, D t -> Rabs ( A t ) <= eta ) ->
  (forall (s : R->R), (forall t, D t -> Rabs (s t - phi t) <= r) ->
                      (forall t, D t -> Rabs ( opeval (opderive F) phi t - opeval (opderive F) s t ) <= lambda1)) ->
  (forall t, D t -> Rabs ( A t * opeval F phi t ) <= d) ->
  0 <= lambda /\ lambda < 1 /\ d + lambda * r <= r ->
  (exists (f: R -> R) ,  forall t, D t  ->  opeval F f t = 0 /\ Rabs ( f t - phi t ) <= d / (1 - lambda)).
 *)
Lemma Requation (x y : R) : x = x - y -> y = 0. 
Proof. simpl. lra. Qed.

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
  have SBP : SBallProp N lambda0 SB.
   apply mkSBallProp.
  + admit.
  + apply R_dcballE => t It /=.
    replace ( _ - _ ) with ( - (A t * opeval F phi t)). rewrite Rabs_Ropp. auto.
    rewrite /N /opnewton opeval_sub opeval_scal /= /f_bin /f_cst. lra. 
  + simpl. replace ( _ + _ ) with ( d / (1 - lambda)) => /=. apply Rle_refl.
    field. lra. 

  move: (BF_lim_is_fixpoint (Hl1 : lambda0 < 1)  SBP) (BF_lim_inside_sball (Hl1 : lambda0 < 1) SBP).
  (*have HA t : I t -> A t <> 0.
  move => It HAt. move : (Hlambda phi). *)
  set bf := lim (banach.BF N lambda0 SB). rewrite /SBall_pred /=. 
  
  move => /Rdomfct_close Hbanach_fix /R_dcballE Hbanach_bound; rewrite /N in Hbanach_fix.
  exists bf; split.
  + move : (Hbanach_fix t). rewrite /opnewton. rewrite opeval_sub opeval_scal opeval_opid /=.  
    intro Hb; apply Requation in Hb => //. admit.
    
  + by apply Hbanach_bound.
Admitted. 
End TubePolyn.
