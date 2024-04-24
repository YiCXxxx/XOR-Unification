(* 

This file Defines the third rewriting rules, UReducing, i.e. remove every C 0 in a lTerm,
and we called the reduced form from UReducing - UReduced,
if a lTerm is UReduced, then every term in the lTerm has no C 0.

Example: 
- [], [V v], [C 1;C 2] is UReduced
- [C1 +' C 0], [C 1 ;C 2; C 3 +' C0] is not UReduced

Then defines the:
- Prop for UReduced
- function for UReducing

And proves the important theorem:

Theorem UReduced_UReducing_alllist: forall(tl:list term),
  AReduced tl -> UReduced (UReducing tl).
  - This Theorem says that after UReducing, every term is UReduced

Theorem UReducing_eqv: forall(tl: list term),
  (UReducing tl) =l= tl.
  - This Theorem says that after UReducing, it is lTerm_eqv to the original lTerm

Theorem UReduced_UReducing: forall (tl :list term),
  UReduced (tl) -> UReducing tl = tl.
  - This Theorem says that UReducing is an idempotent function. 
    This one is not so important at this moment, but it is very crucial for later proof.

Note:
  * Some Theorem takes in an extra assumptions that the lTerm has to be AReduced first.
    This will not affect the rewrite system because in the whole rewrite system we will just do AReducing first.
*)


From XORUnif Require Export NReduced.

(*lTerm [T0] is lTerm_eqv empty lTerm*)
Lemma T0_lTerm_eqv_nil:
  [T0] =l= nil.
Proof.
  intros. apply lTerm_eqv_ok. simpl. rewrite eqvU'. reflexivity.
Qed.

Inductive UReduced: list term-> Prop:=
|UReduced_nil : UReduced []
|NReduced_cons_const : forall (n : nat) (tl : list term), 
    n<>0 -> UReduced tl -> UReduced ((C n) :: tl)
|NReduced_cons_var :  forall (v : var) (tl : list term),
    UReduced tl -> UReduced ((V v) :: tl).

Fixpoint UReducing (tl: list term) : list term:=
  match tl with
  |[] => []
  |t::tl' => if term_beq_syn t T0 then UReducing tl' else t::UReducing tl'
  end.

(* Not Used *)
Lemma UReducing_Correct_Reduced: forall(t:term),
  UReduced (UReducing (term_to_lTerm t)). 
Proof.
  intros. assert(a:=AReducing_Correct_Reduced t). 
  unfold AReducing in a. 
  induction (term_to_lTerm t).
  - simpl. constructor.
  - destruct a0. 
    + simpl. destruct (NatUtil.beq_nat n 0) eqn:Hn0. 
      apply NatUtil.beq_nat_ok in Hn0. inversion a. firstorder.
      constructor. now apply beq_nat_false in Hn0. 
      inversion a. firstorder.
    + simpl. constructor. inversion a. firstorder.
    + inversion a. 
Qed.

(* 
Important theorem about equality 
*)
Theorem UReducing_eqv: forall(tl: list term),
  (UReducing tl) =l= tl.
Proof.
  intros. induction tl.
  - simpl. apply lr_relf. 
  - simpl. destruct (term_beq_syn a T0) eqn:Ht0. 
    + apply term_beq_syn_true_iff in Ht0. rewrite Ht0.
      apply lr_trans with tl. easy. apply (lr_T0 []).
    + apply (lTerm_eqv_cons_compat _ _ _ IHtl).
Qed.


(* 
if a lTerm is UReduced, then remove any term still result in an lTerm 
*)
Lemma UReduced_remove: forall (tl:list term)(t:term),
  UReduced (tl) -> UReduced (remove t tl).
Proof.
  intros. induction H.
  - simpl. constructor.
  - simpl. destruct t. destruct(NatUtil.beq_nat n n0). easy.
    now constructor. now constructor. now constructor.
  - simpl. destruct t. now constructor. destruct(beq_var v v0). easy.
    now constructor. now constructor. 
Qed.

(* Not Used *)
Lemma UReducing_Correct_eqv: forall(t:term),
  t == lTerm_to_term (UReducing (term_to_lTerm t)).
Proof.
  intros. assert(H:=AReduced_Correct_eqv t). rewrite H at 1.
  unfold AReducing. apply lTerm_eqv_ok. 
  assert(a:=UReducing_eqv (term_to_lTerm t)). now apply lr_sym.
Qed.

(*
if an lTerm is AReduced, then UReducing the lTerm will result in UReduced
*)
Theorem UReduced_UReducing_alllist: forall(tl:list term),
  AReduced tl -> UReduced (UReducing tl).
Proof.
  intros. induction tl;simpl.
  - constructor.
  - destruct a.
    + destruct (NatUtil.beq_nat n 0) eqn:H1.
      -- apply NatUtil.beq_nat_ok in H1. unfold T0. rewrite H1. simpl. 
         inversion H;subst. now firstorder.
      -- simpl. rewrite H1. constructor. now apply beq_nat_false in H1. 
         inversion H;subst. now firstorder.
    + simpl. inversion H;subst. constructor. now firstorder.
    + simpl. inversion H.
Qed.

(*
Important theorem about idempotent
*)    
Theorem UReduced_UReducing: forall (tl :list term),
  UReduced (tl) -> UReducing tl = tl.
Proof.
  intros. induction tl.
  - now simpl.
  - inversion H;subst.
    + unfold NReducing. simpl. destruct(NatUtil.beq_nat n 0) eqn:H4.
      -- apply NatUtil.beq_nat_ok in H4. now apply H2 in H4.
      -- firstorder. now rewrite H0.
    + simpl. firstorder. now rewrite H0.
Qed.

(*
simple rewrite rule for UReducing
*)
Lemma UReducing_T0: forall (l1 l2:list term),
  UReducing (l1 ++ T0 :: l2) = UReducing (l1 ++ l2).
Proof.
  intros. induction l1;simpl.
  - auto.
  - destruct (term_beq_syn a T0) eqn:H.
    + easy.
    + now rewrite IHl1.
Qed.

(*
simple rewrite rule for UReducing
*)
Lemma UReducing_nadd0:forall(l:list term),
  UReducing l = UReducing (n_add T0 l).
Proof.
  intros. induction l;simpl.
  - auto.
  - destruct(term_beq_syn a T0) eqn:H;auto. simpl. rewrite H.
    now rewrite IHl.
Qed.

(*
simple rewrite rule for UReducing
*)
Lemma UReducing_app:forall(l1 l2:list term),
  UReducing (l1 ++ l2) = UReducing l1 ++ UReducing l2.
Proof.
  intros. induction l1;simpl. auto.
  destruct(term_beq_syn a T0) eqn:Ha. auto. simpl. now rewrite IHl1.
Qed.

(*
UReducing no order
*)
Lemma UReducing_rev_nil: forall(l:list term),
  UReducing l = [] -> UReducing (rev l) = [].
Proof.
  intros. induction l; simpl. easy.
  assert(H1:=UReducing_T0 (rev l) nil). simpl in H.
  destruct(term_beq_syn a T0) eqn:H2. apply term_beq_syn_true_iff in H2.
  rewrite H2 in *. rewrite H1. rewrite <- app_nil_end.
  apply IHl. easy. destruct (UReducing l). inversion H. inversion H.
Qed.

(*
UReducing and rev homomorphism
*)
Lemma UReducing_rev_homo: forall(l:list term),
  UReducing(rev l) = rev(UReducing l).
Proof.
  intros. induction l;simpl. auto.
  destruct(term_beq_syn a T0)eqn:Ha.
  - apply term_beq_syn_true_iff in Ha. rewrite Ha.
    assert (H3:=UReducing_T0(rev l) nil). rewrite H3. rewrite <- app_nil_end.
    easy.
  - simpl. rewrite UReducing_app. simpl. rewrite Ha. now rewrite IHl.
Qed.


Lemma UReduicng_rev: forall(l1 l2:list term),
  UReducing l1 = UReducing l2 -> UReducing (rev l1) = UReducing (rev l2).
Proof.
  intros l1. pattern l1. induction l1;intro;simpl in *.
  - intros. symmetry. apply UReducing_rev_nil. now symmetry.
  - destruct(term_beq_syn a T0) eqn:Ha. 
    + apply term_beq_syn_true_iff in Ha. rewrite Ha. intros.
      assert(H3:=UReducing_T0(rev l1) nil). rewrite H3.
      rewrite <- app_nil_end. firstorder.
    + intros. rewrite UReducing_app. rewrite UReducing_rev_homo.
      rewrite UReducing_rev_homo.
      rewrite <- H. simpl. now rewrite Ha.
Qed. 

(*
simple rewrite rule for UReducing and NReducing
*)
Lemma UNReducing_T0: forall (l:list term),
  UReducing(NReducing (T0::l)) = UReducing(NReducing l).
Proof.
  intros. induction l.
  - unfold NReducing. now simpl.
  - unfold NReducing. simpl. remember (n_add a (NReducing' l)) as ll.
    apply UReduicng_rev. now rewrite <- UReducing_nadd0. 
Qed.

Lemma UReducing_naddnot0_homo:forall (t:term) (l:list term),
  t<>T0 -> UReducing(n_add t l) = n_add t (UReducing l).
Proof.
  intros. apply term_beq_syn_false_iff in H.
  induction l;simpl.  now rewrite H.
  destruct (term_beq_syn a t) eqn:H1.
  apply term_beq_syn_true_iff in H1. apply term_beq_syn_false_iff in H.
  assert(a <> T0). intro. rewrite <- H1 in H. now rewrite <- H0 in H.
  apply term_beq_syn_false_iff in H0.
  + rewrite H0. rewrite H1. simpl. now rewrite term_beq_syn_relf.
  + destruct (term_beq_syn_dec a T0). apply term_beq_syn_true_iff in e as e2.
    rewrite e. rewrite term_beq_syn_relf. simpl. auto.
    apply term_beq_syn_false_iff in n. rewrite n. simpl.
    rewrite n. rewrite H1. now rewrite IHl.
Qed.

(*
simple rewrite rule for UReducing and NReducing
*)
Lemma UNReducing_T0_mid: forall (l1 l2:list term),
  UReducing(NReducing (l1++T0::l2)) = UReducing(NReducing (l1++l2)).
Proof.
  intros. induction l1.
  - unfold NReducing. simpl. apply UReduicng_rev. now rewrite <- UReducing_nadd0.
  - unfold NReducing. simpl. 
    apply UReduicng_rev. destruct (term_beq_syn_dec a T0).
    + rewrite e. rewrite <- UReducing_nadd0.
      rewrite <- UReducing_nadd0. unfold NReducing in IHl1.
      apply UReduicng_rev in IHl1. rewrite rev_involutive in IHl1.
      now rewrite rev_involutive in IHl1.
    + assert(H1:= UReducing_naddnot0_homo a (NReducing' (l1 ++ T0 :: l2)) n).
      assert(H2:= UReducing_naddnot0_homo a (NReducing' (l1 ++ l2)) n).
      rewrite H1. rewrite H2. f_equal. unfold NReducing in IHl1.
      apply UReduicng_rev in IHl1. rewrite rev_involutive in IHl1.
      now rewrite rev_involutive in IHl1.
Qed.