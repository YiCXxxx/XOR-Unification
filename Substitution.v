(* 

This file mainly handles the utilities for rewriting
e.g. substitutions, lft, Domain, Range, VRan, sub_leq.

*)

From XORUnif Require Export Reduced.
Require Import Coq.Logic.Classical_Prop.


(*
The way we define substitution is a function
takes in a var and return a term just like the definition for substitution
*)
Definition sub : Type := var -> term.

(*
lft function lft the substitution function into a term -> term function
we can simply understand it as apply a substitution to a term
*)
Equations lft (sb:sub):  (term -> term) :=
  lft sb (C n) := C n;
  lft sb (V v) := sb v;
  lft sb (t1 +' t2) := lft sb t1 +' lft sb t2.



(*
however since we have this lTerm data structrue,
lftl is the lTerm version for lft
*)
Definition lftl (sb:sub): lTerm -> lTerm:=
  (fun lt => map (lft sb) lt).

(*
simple intuitive check
*)
Lemma lft_lftl_correct_nat: forall (sb:sub)(n:nat),
  term_to_lTerm (lft sb (C n)) =l= lftl sb (term_to_lTerm (C n)).
Proof.
  intros. simpl. simp lft. simpl. repeat constructor.
Qed.

(*
simple intuitive check
*)
Lemma lft_lftl_correct_var: forall (sb:sub)(v:var),
  term_to_lTerm (lft sb (V v)) =l= lftl sb (term_to_lTerm (V v)).
Proof.
  intros. simpl. simp lft. apply lr_sym.
  apply listTransCorrect_lr_term.
Qed.


(*
Need to prove the lftl and lft transform correctly
*)
Lemma lft_lftl_correct: forall (sb:sub)(t:term),
  term_to_lTerm (lft sb t) =l= lftl sb (term_to_lTerm t).
Proof.
  intros. induction t.
  - apply lft_lftl_correct_nat.
  - apply lft_lftl_correct_var.
  - simpl. simp lft. simpl. assert(H:=lr_compat _ _ _ _ IHt1 IHt2).
    unfold lftl. rewrite map_app. unfold lftl in H. auto.
Qed.


(*
Need to prove the lftl and lft transform correctly
*)
Lemma lftl_lft_correct:forall(sb:sub)(tl:lTerm),
  lTerm_to_term (lftl sb tl) == lft sb (lTerm_to_term tl).
Proof.
  intros. induction tl.
  - simpl. unfold T0. simp lft. reflexivity.
  - simpl. simp lft. apply Oplus_compat. reflexivity. auto.
Qed.




(*
Some basic Lemma for Substitution and lft
*)
Equations id_sub:sub:=
  id_sub v := V v.

Lemma id_is_id_lft:forall (t:term),
  lft id_sub t = t.
Proof.
  intros. induction t;auto. simp lft. congruence. 
Qed.

Lemma id_is_id_lftl:forall (lt:lTerm),
  lftl id_sub lt = lt.
Proof.
  intros. induction lt.
  - auto.
  - simpl. rewrite IHlt. induction a;auto. simp lft. congruence.
Qed.

(*
compose_sub is straight forward, apply sub two times
*)
Definition compose_sub tau2 tau1 : sub :=
  fun v => lft tau2 (tau1 v).

Lemma compose_sub_lft': forall(sb1 sb2:sub)(t:term),
  lft (compose_sub sb1 sb2) t =
  lft sb1 (lft sb2 t).
Proof.
  intros. induction t;auto. simp lft. congruence.
Qed.

Lemma compose_sub_lft: forall(sb1 sb2:sub)(lt:lTerm),
  lftl (compose_sub sb1 sb2) lt =
  lftl sb1 (lftl sb2 lt).
Proof.
  intros. induction lt.
  auto. simpl. rewrite compose_sub_lft'. now f_equal.
Qed.

Lemma compose_ok_var:forall(sb1 sb2:sub)(v:var),
  (compose_sub sb1 sb2) v = lft sb1 (sb2 v).
Proof.
  intros. auto.
Qed.

Lemma compose_sub_assoc: forall(sb1 sb2 sb3:sub),
  compose_sub sb1 (compose_sub sb2 sb3) = 
  compose_sub (compose_sub sb1 sb2) sb3.
Proof.
  intros. apply functional_extensionality. intro. 
  repeat rewrite compose_ok_var. rewrite compose_sub_lft'. auto.
Qed.

Lemma compose_id_r:forall(sb:sub),
  compose_sub sb id_sub = sb.
Proof.
  intros. unfold compose_sub. apply functional_extensionality. intros.
  simp id_sub. simp lft. auto.
Qed.

Lemma compose_id_l:forall(sb:sub),
  compose_sub id_sub sb = sb.
Proof.
  intros. unfold compose_sub. apply functional_extensionality. intros.
  now rewrite id_is_id_lft.
Qed.

Fixpoint var_of (v:var)(t:term):Prop:=
    match t with
    |C n => False
    |V v' => if eq_dec_var v v' then True else False
    |t1 +' t2 => (var_of v t1) \/ (var_of v t2)
    end.

Fixpoint var_of_tl (v:var)(tl:lTerm):Prop:=
  match tl with
  |[] => False
  |t::tl' => var_of v t \/ var_of_tl v tl' 
end.

Definition Id_on_vars (tau:sub) (t:term):=
  (forall v, var_of v t -> tau v = V v).

Lemma Id_on_vars_app:forall (sb:sub)(t1 t2:term),
  Id_on_vars sb (t1 +' t2) <-> Id_on_vars sb t1 /\ Id_on_vars sb t2.
Proof.
  split; intros.
  - unfold Id_on_vars in *. split.
    intros. apply H. simpl. now left. intros. apply H. simpl. now right.
  - destruct H. unfold Id_on_vars in *. intros. simpl in H1. destruct H1.
    + now apply H in H1.
    + now apply H0 in H1.
Qed.

Lemma Id_on_vars_Noop:forall(sb:sub)(t:term),
  Id_on_vars sb t <-> lft sb t = t.
Proof.
  split;intros.
  - induction t;simp lft;auto. unfold Id_on_vars in H. apply H. unfold var_of. 
    destruct (eq_dec_var v v). auto. now apply n. apply Id_on_vars_app in H. destruct H.
    firstorder. congruence.
  - unfold Id_on_vars. intros. induction t. inversion H0. simp lft in H. 
    unfold var_of in H0. destruct (eq_dec_var v v0).
    rewrite e in *. auto. inversion H0.
    simp lft in H. inversion H. firstorder.
Qed.

Definition Id_on_vars_tl (tau: sub) (tl: lTerm) :=
  (forall v, var_of_tl v tl -> lftl tau tl = tl) .

Lemma Id_on_vars_tl_remove:forall(sb:sub)(t:term)(tl:lTerm),
  Id_on_vars_tl sb (t :: tl) -> Id_on_vars_tl sb tl.
Proof.
  intros. unfold Id_on_vars_tl in *. intros. simpl in H.
  assert(lft sb t :: lftl sb tl = t :: tl). apply (H v).
  now right. inversion H1. rewrite H4. auto.
Qed.
    
Lemma Id_on_vars_Noop_tl:forall(sb:sub)(tl:lTerm),
  Id_on_vars_tl sb tl <-> lftl sb tl = tl.
Proof.
  split; intros.
  + unfold Id_on_vars in H. induction tl.
    auto. simpl. f_equal. 
    - unfold Id_on_vars_tl in H.
      unfold lftl in H. simpl in H. apply Id_on_vars_Noop. unfold Id_on_vars. intros.
      assert(J:=H v).
      assert(lft sb a :: map (lft sb) tl = a :: tl). apply J. now left. inversion H1.
      simp lft in H3. apply Id_on_vars_Noop in H3. unfold Id_on_vars in H3.
      apply H3. auto.
    - apply Id_on_vars_tl_remove in H. auto.
  + unfold Id_on_vars_tl. intros. auto.
Qed.

(*
update sub is adding a new pair of bind into exists sub
for example we have substitution
v1 -> t1
adding a new pair of bind v2 -> t2 will becomes
now apply this sub into (v1+'v2) we get (t1+'t2)
*)
Equations update_sub : sub -> var -> term -> sub :=
  update_sub tau x t := 
    fun v => if eq_dec_var x v then
               t else
               tau v.

Lemma update_eq tau x t :
  lft (update_sub tau x t) (V x) = t.
Proof.
 simp update_sub.
 simp lft.
 now destruct (eq_dec_var x x).
Qed.

Lemma update_neq tau x t x1 :
  x <> x1 ->
  lft (update_sub tau x t) (V x1) = 
    lft tau (V x1).
Proof.
intros H;
 simp update_sub;  simp lft;
   destruct (eq_dec_var x x1); auto; congruence.
Qed.

Definition singleton_sub (x: var) (t: term) : sub :=
  update_sub id_sub x t.

Lemma Reduced_Ord_remove:forall(t:term)(tl:lTerm),
  Reduced_Ord(t::tl) -> Reduced_Ord(tl).
Proof.
  intros. inversion H;subst. apply Reduced_Ord_All. apply Reduced_cons in H0. auto.
  now apply ltSorted_remove in H1.
Qed.

Lemma Reduced_Ord_app:forall(tl1 tl2:lTerm),
  Reduced_Ord(tl1++tl2) -> Reduced_Ord tl1 /\ Reduced_Ord tl2.
Proof.
  intros. induction tl1;simpl in *.
  - split;auto. repeat constructor.
  - split. apply Reduced_Ord_remove in H as H1. apply IHtl1 in H1. destruct H1.
    inversion H;subst. inversion H2;subst. 
    repeat constructor.
    + destruct a;try constructor; inversion H0;subst; inversion H7;auto. inversion H4.
    + inversion H5;subst; apply ListUtil.notin_app in H9;destruct H9;
      inversion H0;subst; inversion H9;subst;constructor;auto.
    + inversion H0;subst;inversion H7;subst; inversion H6;subst; constructor;auto.
    + assert(K:=ltSorted_break (a::tl1) tl2 H3). now destruct K.
    + apply Reduced_Ord_remove in H as H1. firstorder.
Qed.
    

Lemma singleton_sub_not_dom:forall(v:var)(tl:lTerm)(t:term),
  Reduced_Ord tl -> 
  ~ In (V v) tl -> 
  lftl (singleton_sub v t) tl = tl.
Proof.
  intros v tl. generalize dependent v. induction tl;intros;simpl in *.
  auto. f_equal.
  - inversion H;subst. inversion H1;subst. apply NReduced_NoDup in H4. clear H1 H2 H5 IHtl.
    destruct a. 
    + simp lft. auto.
    + destruct (eq_dec_var v v0). exfalso. apply H0. left. now rewrite e. unfold singleton_sub.
      assert(J:=update_neq id_sub v t v0 n). rewrite J. rewrite id_is_id_lft. auto.
    + inversion H3. 
  - apply IHtl. now apply Reduced_Ord_remove in H. intro. apply H0. now right.
Qed.


(*
to determ domain of a var is just testing if this sub will map this var to some different term
because we have the definition for domain that sig(v)<>v
*)
Definition Dom (tau: sub)(v: var) : Prop :=
  tau(v) <>  (V v).


Definition Domb (tau: sub):  var -> bool :=
  fun v => negb (term_beq_syn (tau v) (V v)). 

(** *** Decidability of [Dom] *)
#[export]
Instance domOLD_dec tau v : Decbl (Dom tau v).
Proof.
  destruct (term_beq_syn_dec (tau v) (V v)) eqn: e; auto.
Qed.

Inductive DomI  (tau: sub)(v: var) : Prop :=
  DomC :  tau(v) <>  (V v) -> DomI tau v .

#[export]
Instance domI_dec tau v : Decbl (DomI tau v).
Proof.
 unfold Decbl.
 destruct (term_beq_syn_dec (tau v) (V v)) eqn: e.
 -  right.
    intros H; inversion H; auto.
 - left. constructor. auto.
Qed.


Definition disjoint {T: Type} (P Q : T -> Prop) : Prop :=
  forall t, (P t) -> (Q t ) -> False.

Lemma disjoint_dom_Noop (tau: sub) (t: term) :
  (disjoint (Dom tau) (fun x => var_of x t)) ->
  lft tau t  = t.
Proof.  
  generalize dependent t;intros.
  induction t;simp lft;auto.
  - unfold disjoint in H. assert(J:=H v).
    unfold Dom in J. unfold var_of in J. 
    destruct (term_beq_syn_dec (tau v) (V v)).
    auto. apply J in n. inversion n. destruct (eq_dec_var v v). 
    auto. now apply n0.
  - rewrite IHt1. rewrite IHt2. auto.
    -- clear IHt1. unfold disjoint in *. intros. assert(J:= H t).
       apply J. auto. simpl. now right.
    -- clear IHt2. unfold disjoint in *. intros. assert(J:= H t).
       apply J. auto. simpl. now left.
Qed.

Lemma disjoint_dom_Noop_tl (tau: sub) (tl: lTerm) :
  (disjoint (Dom tau) (fun x => var_of_tl x tl)) ->
  lftl tau tl  = tl.
Proof.
  intros. unfold disjoint in H. 
  induction tl. auto.
  simpl. f_equal.
  - clear IHtl. apply Id_on_vars_Noop. unfold Id_on_vars. intros.
    assert(J:= H v). unfold Dom in J. destruct (term_beq_syn_dec (tau v) (V v)).
    auto. apply J in n. inversion n. simpl. now left.
  - apply IHtl. intros. unfold Dom in H0. apply (H t). auto. simpl. now right.
Qed.
  
(*
to determ range of a sub similar
we just need to check it is not appears anywhere on the range of the substitution
*)
Inductive Ran (tau: sub) : term -> Prop :=
  | RanC : forall (v: var),
      Dom tau v -> Ran tau (tau v).


Inductive Vran (tau: sub) (v : var) : Prop :=
  | VRanC (t: term): (Ran tau t) ->
                     var_of v t ->
                     Vran tau v.

Lemma vran_var_of (tau: sub) (x v: var) :
   Dom tau x ->
   var_of v (tau x) -> 
   Vran tau v.
Proof.
  intros; now apply VRanC with (tau x).
Qed.

Definition idempotent (tau: sub) : Prop :=
  (compose_sub tau tau) = tau.


Definition dom_vran_disjoint  (tau: sub) : Prop :=
  forall (x: var),
    Dom tau x ->
    Vran tau x -> False.


Lemma not_dom (tau: sub) (x: var) :
 ~ Dom tau x ->
  tau x = V x.
Proof.
  unfold Dom. intros H.
  apply dec_DN.
  - apply term_beq_syn_dec.
  - auto.
Qed.

Lemma noop_lft (tau: sub) (t: term) :
  (forall x, var_of x t  -> ~ Dom tau x)
    -> lft tau t = t.
Proof.
  intros. apply Id_on_vars_Noop. unfold Id_on_vars. intros.
  assert(J:=H v). apply J in H0 as H1. apply not_dom in H1. auto.
Qed.


Lemma noop_lft_tl(tau:sub)(tl:lTerm):
  (forall x, var_of_tl x tl -> ~ Dom tau x)
    -> lftl tau tl = tl.
Proof.
  intros. induction tl. auto.
  simpl in *. f_equal.
  - induction a;simp lft. auto. apply not_dom. apply H.
    left. simpl. destruct(eq_dec_var v v). auto. now apply n.
    rewrite IHa1. rewrite IHa2. auto.
    + intros. apply H. destruct H0. left. simpl. now right. now right.
    + intros. apply H. destruct H0. left. simpl. now left. now right.
  - apply IHtl. intros. apply H. now right.
Qed.


Lemma dom_vran_helper  (tau: sub) (x: var) :
  dom_vran_disjoint tau ->
  Dom tau x ->
  lft tau (tau x) = tau x.
Proof.
  intros H H1. apply noop_lft. intros.
  unfold dom_vran_disjoint in H. intro. apply (H x0);auto.
  apply VRanC with (tau x). apply RanC. auto. auto.
Qed.

Lemma dom_vran_idempotent  (tau: sub):
  dom_vran_disjoint tau  ->
  idempotent tau.
Proof.
  intros. unfold idempotent. unfold dom_vran_disjoint in H.
  unfold compose_sub. apply functional_extensionality. intros.
  destruct (dcd (Dom tau x)).
  - apply dom_vran_helper;auto.
  - assert(H1:=Id_on_vars_Noop tau (V x)).
    assert(tau x = (V x)).
    + apply not_dom. auto.
    + rewrite H0. simp lft.
Qed.
    
Lemma idempotent_dom_vram (tau: sub):
  idempotent tau ->
  dom_vran_disjoint tau.
Proof.
  intros Hid. unfold idempotent in Hid. unfold dom_vran_disjoint. 
  intros x Hd Hv.  
  inversion Hv;subst. clear Hv. inversion H;subst. clear H.
  assert((compose_sub tau tau) v = tau v ).
  rewrite Hid. auto. unfold compose_sub in H. apply Id_on_vars_Noop in H.
  unfold Id_on_vars in H.   
  assert(J:= Id_on_vars_Noop tau (tau v)). apply H in H0 as H2. unfold Dom in *.
  now apply Hd in H2.
Qed.

Lemma idempotent_dom_vram_disjoint_correct(tau:sub):
  idempotent tau <-> dom_vran_disjoint tau .
Proof.
  split.
  - apply idempotent_dom_vram.
  - apply dom_vran_idempotent.
Qed.

Definition leq_sub (eta tau: sub) : Prop :=
  exists gamma, (compose_sub gamma eta) = tau.

Definition leq_sub_xor (eta tau: sub) : Prop :=
  forall (v:var), 
    exists gamma, (compose_sub gamma eta) v == tau v.

Lemma leq_sub_refl (tau : sub) :
    leq_sub tau tau.
Proof.
  exists id_sub. apply compose_id_l.
Qed.

Lemma leq_sub_trans (eta tau gamma : sub) :
     leq_sub eta tau ->
     leq_sub tau gamma  ->
     leq_sub eta gamma .
Proof.
  intros. unfold leq_sub in *.
  destruct H. destruct H0.
  exists (compose_sub x0 x). 
  rewrite <- compose_sub_assoc. now rewrite H.
Qed.




