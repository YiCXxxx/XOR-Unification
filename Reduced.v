(* 

This file put all rewrite system together and proves the most important Lemma:

Theorem lTerm_eqv_eq_correct: forall (l1 l2:list term),
  l1 =l= l2 <-> Reducing_lr_Ord l1 = Reducing_lr_Ord l2.

i.e. Every two lTerm that is equivalence IFF their Reduced form are equal.
*)

From XORUnif Require Export list.

(*
Reduced is just being AReduced NReduced URedcued at the same time
*)
Inductive Reduced: list term-> Prop:=
|Reduced_All: forall (tl:list term), 
  AReduced tl -> NReduced tl -> UReduced tl-> Reduced tl.

(* Not Used *)
Definition Reducing (t:term):list term:=
  UReducing (NReducing (term_to_lTerm t)).

(* Not Used *)
Lemma AReducing_NReducing_AReduced: forall(t:term),
  AReduced (term_to_lTerm t) -> AReduced (NReducing (term_to_lTerm t)).
Proof.
  intros. induction (term_to_lTerm t).
  - now simpl.
  - simpl. destruct (In_dec a (NReducing' l)).
    + apply n_add_In in i. unfold NReducing in *. apply AReduced_rev. simpl.
      rewrite i. apply AReduced_remove. inversion H; firstorder; apply AReduced_rev in H3;
      now rewrite rev_involutive in H3. 
    + apply n_add_not_In in n. unfold NReducing in *. apply AReduced_rev. simpl.
      rewrite n. 
      apply AReduced_app. inversion H;subst;firstorder; apply AReduced_rev in H0;
      now rewrite rev_involutive in H0.
      inversion H; repeat constructor.
Qed.

(* Not Used *)
Lemma AReducing_UReducing_AReduced: forall(t:term),
  AReduced (term_to_lTerm t) -> AReduced (UReducing (term_to_lTerm t)).
Proof.
  intros. induction (term_to_lTerm t).
  - simpl. constructor.
  - simpl. destruct (term_beq_syn a T0) eqn:H1.
    + inversion H;firstorder.
    + inversion H; constructor; firstorder.
Qed.

(* 
if a lTerm is AReduced, then after NReducing it, it remains AReduced
*)
Lemma AReducing_NReducing_AReduced_list: forall(tl:list term),
  AReduced tl -> AReduced (NReducing tl).
Proof.
  intros. induction tl;simpl.
  - easy.
  - unfold NReducing in *. apply AReduced_rev.
    destruct (In_dec a (NReducing' tl));simpl.
    + apply n_add_In in i. rewrite i. apply AReduced_remove. inversion H;subst;
      firstorder; apply AReduced_rev in H0; now rewrite rev_involutive in H0.
    + apply n_add_not_In in n. rewrite n. simpl. 
      apply AReduced_app. inversion H;subst;firstorder;
      apply AReduced_rev in H0; now rewrite rev_involutive in H0. 
      inversion H; repeat constructor.
Qed.

(* 
if a lTerm is AReduced, then after UReducing it, it remains AReduced
*)

Lemma AReducing_UReducing_AReduced_list: forall(tl: list term),
  AReduced tl -> AReduced (UReducing tl).
Proof.
  intros. induction tl.
  - simpl. constructor.
  - simpl. destruct (term_beq_syn a T0) eqn:H1.
    + inversion H;firstorder.
    + inversion H; constructor; firstorder.
Qed.

(*
if a term is not in lTerm, then it is not in UReducing lTerm
*)

Lemma not_In_URducing: forall (tl:list term) (t:term),
  ~ In t tl -> ~ In t (UReducing tl).
Proof.
  intros. intro. apply H. induction tl.
  - inversion H0.
  - simpl in *. destruct (term_beq_syn a T0).
    + apply Decidable.not_or in H. destruct H. firstorder.
    + apply Decidable.not_or in H. destruct H. inversion H0.
      now left. firstorder.
Qed.

(* 
if a lTerm is NReduced, then after UReducing it, it remains NReduced
*)

Lemma NReducing_UReducing_AReduced_list: forall(tl: list term),
  NReduced tl -> NReduced (UReducing tl).
Proof.
  intros. induction tl.
  - simpl. constructor.
  - inversion H;subst;firstorder. 
    + simpl. destruct (NatUtil.beq_nat n 0) eqn:H1. easy. 
      constructor. now apply not_In_URducing. easy.
    + simpl. constructor. now apply not_In_URducing. easy.
Qed.

Lemma UReducing_Correct_list: forall (tl:list term),
  AReduced tl -> UReduced(UReducing tl).
Proof.
  apply UReduced_UReducing_alllist.
Qed.

(* Not Used *)
Lemma Reducing_Correct_Reduced: forall(t:term),
  Reduced (Reducing t). 
Proof.
  intros. constructor.
  - unfold Reducing. assert(H0:=AReducing_Correct_Reduced t).
    assert(H:=AReducing_NReducing_AReduced t H0).
    now assert(H1:=AReducing_UReducing_AReduced_list (NReducing (term_to_lTerm t)) H).
  - unfold Reducing. assert(H:=NReducing_Correct_Reduced t). 
    now assert(H1:=NReducing_UReducing_AReduced_list (NReducing (term_to_lTerm t)) H).
  - unfold Reducing.
    assert(H0:=AReducing_Correct_Reduced t).
    assert(H1:=AReducing_NReducing_AReduced t H0). 
    now apply UReducing_Correct_list in H1.
Qed.

(* Not Used *)
Lemma UReducing_Correct_eqv: forall(t:term),
  t == lTerm_to_term (Reducing t).
Proof.
  intros. unfold Reducing.
  assert(H:=AReduced_Correct_eqv t).
  assert(H1:=NReducing_eqv (AReducing t)).
  assert(H2:=UReducing_eqv (NReducing (AReducing t))).
  rewrite H at 1. apply lTerm_eqv_ok. apply lr_sym in H1,H2.
  now assert(a:=lr_trans (AReducing t) (NReducing (AReducing t)) 
        (UReducing (NReducing (AReducing t))) H1 H2).
Qed.

(* Reducing_lr for input lTerm output lTerm *)
Definition Reducing_lr (tl:list term):list term:=
  UReducing (NReducing (AReducing_lr tl)).

(* Important theorem about Reducing_lr correctly reduced*)
Theorem Reducing_lr_Correct_Reduced: forall(tl:list term),
  Reduced(Reducing_lr tl).
Proof.
  intros. constructor.
  - unfold Reducing_lr. assert(H0:=AReducing_lr_Correct_Reduced tl).
    assert(H:=AReducing_NReducing_AReduced_list (AReducing_lr tl) H0).
    now assert(H1:=AReducing_UReducing_AReduced_list (NReducing (AReducing_lr tl))H).
  - unfold Reducing_lr. assert(H0:=AReducing_lr_Correct_Reduced tl).
    assert(H:=NReducing_Correct_alllist (AReducing_lr tl) H0). 
    now assert(H1:=NReducing_UReducing_AReduced_list (NReducing (AReducing_lr tl)) H).
  - unfold Reducing_lr.
    assert(H0:=AReducing_lr_Correct_Reduced tl).
    assert(H1:=AReducing_NReducing_AReduced_list (AReducing_lr tl) H0). 
    now apply UReducing_Correct_list in H1.
Qed.

(*
Important theorem about equivalence relations does not change
*)
Theorem Reducing_lr_Correct_eqv: forall(tl:list term),
  tl =l= (Reducing_lr tl).
Proof.
  intros. unfold Reducing_lr.
  assert(H:=AReducing_lr_Correct_eqv tl).
  assert(H1:=NReducing_eqv (AReducing_lr tl)).
  assert(H2:=UReducing_eqv (NReducing (AReducing_lr tl))). apply lr_sym in H1,H2.
  assert(H3:=lr_trans tl (AReducing_lr tl) (NReducing (AReducing_lr tl)) H H1).
  apply lr_trans with (NReducing (AReducing_lr tl));easy.
Qed.

(*
Simple rewrite rule about reducing lr
*)
Lemma Reducing_lr_nil:
  Reducing_lr ( [] ) = [].
Proof.
  intros. unfold Reducing_lr. now simpl.
Qed.

(*
Simple rewrite rule about reducing lr
*)
Lemma Reducing_lr_T0:
  Reducing_lr ( [T0] ) = [].
Proof.
  intros. unfold Reducing_lr. now simpl.
Qed.

(*
Some simple implication about reduced
*)
Lemma Reduced_cons: forall (t:term) (tl:list term),
Reduced (t::tl) -> Reduced tl.
Proof.
  intros. inversion H;subst. constructor.
  - inversion H0;subst. easy. easy.
  - inversion H1;subst. easy. easy.
  - inversion H2;subst. easy. easy.
Qed.

Lemma Reduced_NoDup: forall(tl:list term),
  Reduced (tl) -> NoDup tl.
Proof.
  intros. inversion H;subst. 
  induction tl.
  - constructor.
  - destruct (In_dec a tl).
    + inversion H1;subst. now apply H5 in i. now apply H5 in i. 
    + constructor. easy. apply Reduced_cons in H. inversion H;subst.
      firstorder.
Qed.

(*
Now we define our reduced form for all of our rewrite rule
AReduced/\NReduced/\UReduced/\ltSorted
*)

Inductive Reduced_Ord: list term -> Prop:=
|Reduced_Ord_All: forall (tl:list term), 
  Reduced tl -> ltSorted tl -> Reduced_Ord tl.

Lemma Reduced_Ord_cons: forall (t:term) (tl:list term),
  Reduced_Ord (t::tl) -> Reduced tl.
Proof.
  intros. inversion H. now apply Reduced_cons in H0.
Qed.


(*
Not Used
*)
Fixpoint term_Inb (tl: list term)(t:term) : bool :=
  match tl with 
  |[] => false
  |t'::tl' => if term_beq_syn t t' then true else term_Inb tl' t
  end.

Lemma term_Inb_In_complete:forall (tl:list term)(t:term),
  In t tl -> term_Inb tl t = true.
Proof.
  intros. induction tl.
  - inversion H.
  - inversion H.
    + simpl. rewrite H0. now rewrite term_beq_syn_relf.
    + simpl. destruct (term_beq_syn_dec t a). 
      ++ rewrite e. now rewrite term_beq_syn_relf.
      ++ apply term_beq_syn_false_iff in n. rewrite n. now apply IHtl.
Qed.

Lemma term_Inb_In_sound:forall (tl:list term)(t:term),
  term_Inb tl t = true -> In t tl.
Proof.
  intros. induction tl.
  - now simpl in H.
  - destruct (term_beq_syn_dec t a).
    + simpl. now left.
    + simpl. right. apply IHtl. inversion H. apply term_beq_syn_false_iff in n.
      now rewrite n in *.
Qed. 

Lemma term_Inb_In_Correct: forall (tl:list term)(t:term),
  term_Inb tl t = true <-> In t tl.
Proof.
  intros. split.
  - apply term_Inb_In_sound.
  - apply term_Inb_In_complete.
Qed.

Fixpoint fold {X Y: Type} (f : X->Y->Y) (l : list X) (b : Y): Y :=
match l with
| nil => b
| h :: t => f h (fold f t b)
end.

Definition incl_bool(l1 l2:list term):bool:=
  fold andb (map (term_Inb l2) l1) true.

Lemma incl_bool_prop_complete: forall(l1 l2:list term),
  incl l1 l2 -> incl_bool l1 l2 = true.
Proof.
  intros l1. pattern l1. induction l1.
  - intros. unfold incl in H. unfold incl_bool. now simpl.
  - intros l3 H. unfold incl in H.  
    simpl in H.  unfold incl_bool. simpl.
    apply andb_true_iff. split.
    + apply term_Inb_In_complete. apply H. now left.
    + apply IHl1. unfold incl. intros. apply H. now right.
Qed.


Lemma incl_bool_prop_sound: forall(l1 l2:list term),
  incl_bool l1 l2 = true -> incl l1 l2.
Proof.
  intros l1. pattern l1. induction l1.
  - intros. unfold incl. now intro.
  - intros. apply incl_cons.
    + unfold incl_bool in H. simpl in H.
      apply andb_true_iff in H. destruct H. now apply term_Inb_In_sound.
    + apply IHl1. unfold incl_bool in H. simpl in H.
      apply andb_true_iff in H. now destruct H. 
Qed.

Lemma incl_bool_prop_correct: forall(l1 l2:list term),
  incl_bool l1 l2 = true <-> incl l1 l2.
Proof.
  intros; split. 
  - apply incl_bool_prop_sound.
  - apply incl_bool_prop_complete.
Qed.

(*
function returns if two lTerm are Exactly the same
*)
Fixpoint term_beq_syn_list(l1 l2:list term):bool:=
  match l1, l2 with
  |nil, nil => true
  |_ , nil => false
  |nil, _ => false
  |t1::l1', t2::l2' => if term_beq_syn t1 t2 
                        then term_beq_syn_list l1' l2'
                        else false
  end.

(*
Simple lemma about correctness of function term_beq_syn_list
*)
Lemma term_beq_syn_list_sound: forall (l1 l2:list term),
  term_beq_syn_list l1 l2 = true -> l1 = l2.
Proof.
  intros l1. pattern l1. induction l1.
  - intros. inversion H. destruct l2. auto. inversion H1.
  - intros. destruct l2. inversion H. simpl in H. 
    destruct(term_beq_syn a t) eqn:H1. 
    + apply term_beq_syn_sound in H1. f_equal; auto.
    + inversion H.
Qed.

(*
Simple lemma about correctness of function term_beq_syn_list
*)
Lemma term_beq_syn_list_complete: forall (l1 l2:list term),
  l1 = l2 -> term_beq_syn_list l1 l2 = true.
Proof.
  intros. rewrite H. clear H. induction l2;auto.
  simpl. now rewrite term_beq_syn_relf.
Qed.

(*
Simple lemma about correctness of function term_beq_syn_list
*)
Lemma term_beq_syn_list_correct: forall (l1 l2:list term),
  l1 = l2 <-> term_beq_syn_list l1 l2 = true.
Proof.
  split. apply term_beq_syn_list_complete. apply term_beq_syn_list_sound.
Qed.


(*
This is the final version of our rewrite rule
*)
Definition Reducing_lr_Ord (l:list term):list term:=
  sort_term (Reducing_lr l).


(*
There will be a lot of Helper lemma,
only will highlight the most important part.
*)
Lemma NReduced_app:forall(lt1 lt2:lTerm),
  NReduced(lt1++lt2)-> NReduced lt1 /\ NReduced lt2.
Proof.
  split;intros. 
  - induction lt1. constructor. simpl in *. inversion H;subst;
    constructor; apply ListUtil.notin_app in H2; now destruct H2; auto.
  - induction lt1. auto. inversion H;subst;auto.
Qed.
  
Lemma UReduced_app:forall(lt1 lt2:lTerm),
  UReduced(lt1++lt2)-> UReduced lt1 /\ UReduced lt2.
Proof.
  split; intros. 
  - induction lt1. constructor. simpl in *. inversion H;subst.
    constructor;auto. constructor ;auto.
  - induction lt1. auto. inversion H;subst;auto.
Qed. 
  
Lemma Reduced_app:forall(lt1 lt2:lTerm),
  Reduced(lt1++lt2) -> Reduced lt1 /\ Reduced lt2.
Proof.
  intros. inversion H;subst. 
  apply AReduced_app_back_left in H0 as A1.
  apply AReduced_app_back_right in H0 as A2.
  apply NReduced_app in H1.
  apply UReduced_app in H2.
  destruct H1. destruct H2. split; now constructor.
Qed.

Lemma Permutation_Reduced:forall(lt1 lt2 :lTerm),
  Permutation lt1 lt2 -> Reduced lt1 -> Reduced lt2.
Proof.
  intros. induction H.
  - constructor;constructor.
  - inversion H0;subst. apply Reduced_cons in H0. firstorder. inversion H4;subst.
    inversion H1;subst;
    inversion H2;subst; inversion H3;subst;
    constructor;constructor;auto. 
    assert(J:=Permutation_Not_In l l' (C n) H H11). auto.
    assert(J:=Permutation_Not_In l l' (V v) H H11). auto.
  - inversion H0;subst. constructor.
    + clear H0 H1 H2. inversion H;subst;inversion H1;subst;
      constructor;constructor;auto.
    + clear H0 H H2. inversion H1;subst; inversion H3; subst; apply not_in_cons in H2; 
      destruct H2; constructor; try constructor; auto;intro.
      destruct H2. now apply H. now apply H4. 
      destruct H2. now apply H. now apply H4. 
      destruct H2. now apply H. now apply H4. 
      destruct H2. now apply H. now apply H4.
    + clear H0 H1 H. inversion H2; subst. inversion H3;subst;constructor;try constructor; auto.
      inversion H0. constructor;auto. constructor. auto. constructor;constructor. auto.
  - firstorder.
Qed.
  

Lemma Reduced_sort_term_Reduced:forall(lt:lTerm),
  Reduced lt -> Reduced (sort_term lt).
Proof.
  intros. inversion H;subst. apply (sort_ltSorted_Permutation) in H0. 
  apply Permutation_Reduced in H0;auto.
Qed.


(* =============================================================================== *)
(*
Important theorem about Reducing_lr_Ord correctly reduced the term
*)
Theorem Reducing_lr_Ord_Correct_Reduced_Ord: forall(lt:lTerm),
  Reduced_Ord (Reducing_lr_Ord lt).
Proof.
  intros. assert (J:=Reducing_lr_Correct_Reduced lt).
  unfold Reducing_lr_Ord. apply Reduced_sort_term_Reduced in J. 
  constructor. auto. apply sort_ltSorted.
Qed.

(*
Important theorem about Reducing_lr_Ord being idempotent
*)
Theorem Reduced_Ord_Reducing_lr_Ord: forall(tl:lTerm),
    Reduced_Ord tl -> Reducing_lr_Ord tl = tl.
Proof.
  intros. inversion H. inversion H0;subst.
  unfold Reducing_lr_Ord. unfold Reducing_lr.
  apply AReduced_AReducing_idpt in H3 as J. rewrite J.
  apply NReduced_NReducing in H4. rewrite H4.
  apply UReduced_UReducing in H5. rewrite H5.
  assert(K:=ltSorted_sort_term tl H3 H1). auto.
Qed.

(*
Simple connecting Lemma
*)
Lemma Reducing_lr_Ord_Reducing_lr_eqv: forall(tl:list term),
  lTerm_eqv (Reducing_lr tl) (Reducing_lr_Ord tl).
Proof.
  intros. unfold Reducing_lr_Ord. 
  assert(H:=Reducing_lr_Correct_Reduced tl).
  inversion H. 
  assert(H5:=sort_ltSorted_Permutation _ H0). now constructor.
Qed.

(*
Important theorem about Reducing_lr_Ord being equivalence
*)

Theorem Reducing_lr_Ord_Correct_eqv: forall(tl:list term),
  tl =l= (Reducing_lr_Ord tl).
Proof.
  intros. unfold Reducing_lr_Ord.
  apply lr_trans with (Reducing_lr tl).
  - apply Reducing_lr_Correct_eqv.
  - apply Reducing_lr_Ord_Reducing_lr_eqv.
Qed.
(* =============================================================================== *)


(*
Next we want to prove that if two terms are equivalence then theire reduced form are equal
*)

(*
This function takes in two terms and return true if their reduced form are equal, false otherwise
*)
Definition lTerm_eqv_bool(l1 l2:list term):bool:=
  term_beq_syn_list (Reducing_lr_Ord l1) (Reducing_lr_Ord l2).

Lemma lTerm_eqv_bool_relf:forall (lt:list term),
  lTerm_eqv_bool lt lt = true.
Proof.
  intros. unfold lTerm_eqv_bool. now apply term_beq_syn_list_correct.
Qed.

Lemma lTerm_eqv_bool_sym:forall (lt1 lt2:list term),
  lTerm_eqv_bool lt1 lt2 = true -> lTerm_eqv_bool lt2 lt1 = true.
Proof.
  intros. apply term_beq_syn_list_correct in H. unfold lTerm_eqv_bool.
  rewrite H. apply lTerm_eqv_bool_relf. 
Qed.


(*
The other direction is easy, because we can directly rewrite
*)
Lemma lTerm_eqv_bool_sound: forall (l1 l2:list term),
  lTerm_eqv_bool l1 l2 = true -> lTerm_eqv l1 l2.
Proof.
  intros.
  apply term_beq_syn_list_correct in H. 
  assert(H1:=Reducing_lr_Ord_Correct_eqv l1).
  assert(H2:=Reducing_lr_Ord_Correct_eqv l2). rewrite H in H1.
  apply lr_trans with (Reducing_lr_Ord l2);auto. now apply lr_sym.
Qed.


(*
Again there are lots of helper lemma here
Only will highlight the important theorem
*)
Lemma Reducing_lr_Ord_T0_cons: forall (l:list term),
  Reducing_lr_Ord (T0 :: l) = Reducing_lr_Ord (l).
Proof.
  intros. unfold Reducing_lr_Ord. simpl. induction l;simpl.
  - rewrite Reducing_lr_T0. now rewrite Reducing_lr_nil.
  - unfold Reducing_lr. assert(H:=AReducing_lr_app [T0] (a::l)). 
    assert( AReducing_lr ([T0] ++ a :: l) = AReducing_lr (T0 :: a :: l) ).
    {now simpl. }
    rewrite <- H0. rewrite <- H. simpl AReducing_lr at 1. 
    clear H H0. remember (AReducing_lr (a :: l)) as ll.
    assert(T0::ll=[T0]++ll). now simpl. rewrite <- H. 
    now rewrite UNReducing_T0. 
Qed.


Lemma NoDup_NReducing'_idpt:forall (l:list term),
  NoDup l -> NReducing' l = rev l.
Proof.
  intros. induction H;simpl. auto. apply not_In_Reduced in H. 
  apply n_add_not_In in H. rewrite H. now rewrite IHNoDup.
Qed.

Lemma NReducing_listsame:forall(l:list term),
  NReducing (l++l) = [].
Proof. 
  intros. induction l.
  - unfold NReducing. now simpl.
  - unfold NReducing in *. 
    apply rev_f_equal. rewrite rev_involutive. apply NReducing'_listsame.
Qed.

Lemma Permutation_preserve_UReducing: forall (tl1 tl2:list term),
  Permutation tl1 tl2 -> Permutation (UReducing tl1) (UReducing tl2).
Proof.
    intros. induction H; simpl.
    + constructor. 
    + destruct(term_beq_syn x T0);auto. 
    + destruct(term_beq_syn y T0);destruct(term_beq_syn x T0). apply Permutation_relf.
      constructor. apply Permutation_relf. constructor. apply Permutation_relf.
      constructor.
    + apply perm_trans with (UReducing l');auto.
Qed.

Lemma Permutation_preserve_NReducing': forall (tl1 tl2:list term),
  Permutation tl1 tl2 -> Permutation (NReducing' tl1) (NReducing' tl2).
Proof.
  intros. induction H;simpl.
  - constructor.
  - remember (NReducing' l) as nl. remember (NReducing' l') as nl'.
    destruct (In_dec x nl); clear Heqnl Heqnl'.
    -- assert(H1:=Permutation_In nl nl' x). apply H1 in IHPermutation as H2;auto.
       apply n_add_In in i. apply n_add_In in H2. rewrite i. rewrite H2.
       now apply Permutation_remove_sym.
    -- assert(H1:= Permutation_Not_In nl nl' x). firstorder.
       apply n_add_not_In in n. apply n_add_not_In in H0.
       rewrite n. rewrite H0. now apply Permutation_app_tail.
  - remember (NReducing' l) as tl. clear Heqtl. induction tl;simpl.
    + destruct(term_beq_syn x y) eqn:H. apply term_beq_syn_true_iff in H. rewrite H.
      rewrite term_beq_syn_relf. constructor. apply term_beq_syn_false_iff in H.
      apply not_eq_sym in H. apply term_beq_syn_false_iff in H. rewrite H. constructor.
    + destruct(term_beq_syn a x) eqn:H. 
      -- apply term_beq_syn_true_iff in H. rewrite H. destruct (term_beq_syn x y) eqn:H1.
        ++ apply term_beq_syn_true_iff in H1. rewrite H1. apply Permutation_relf.
        ++ simpl. rewrite term_beq_syn_relf. apply Permutation_relf.
      -- apply term_beq_syn_false_iff in H. destruct(term_beq_syn a y) eqn:H1.
        ++ apply term_beq_syn_true_iff in H1. rewrite H1. simpl. rewrite term_beq_syn_relf.
           apply Permutation_relf.
        ++ simpl. apply term_beq_syn_false_iff in H. rewrite H. rewrite H1. now constructor.
  - apply perm_trans with (NReducing' l'); auto.
Qed.

Definition Permutation_remove_fequal{X:Type}: forall (l1 l2 :list X),
  Permutation l1 l2 -> Permutation (rev l1) (rev l2).
Proof.
  intros. rewrite <- Permutation_rev. rewrite <- Permutation_rev. auto.
Qed.

Lemma Reducing_lr_Ord_term_swap: forall(t1 t2:term),
  Reducing_lr_Ord [t1 +' t2] = Reducing_lr_Ord [t2 +' t1].
Proof.
  intros. unfold Reducing_lr_Ord.
  unfold Reducing_lr. simpl. rewrite app_nil_r. rewrite app_nil_r. 
  remember (term_to_lTerm t1) as lx. remember (term_to_lTerm t2) as ly.
  clear Heqlx Heqly. unfold NReducing. 
  assert(Permutation (UReducing (rev (NReducing' (lx ++ ly))))(UReducing (rev (NReducing' (ly ++ lx))))).
  + apply Permutation_preserve_UReducing. apply Permutation_remove_fequal. 
    apply Permutation_preserve_NReducing'. apply Permutation_app_comm.
  + now apply Permutation_sort_same.
Qed.


Lemma term_to_lTerm_Oplus: forall (t:term),
  Oplus_term t = false -> term_to_lTerm t = [t].
Proof.
  intros. destruct t; auto. inversion H.
Qed.


Lemma Reducing_lr_Ord_oplus:forall(x y:term),
  Reducing_lr_Ord [x +' y] = Reducing_lr_Ord [x;y].
Proof.
  intros. unfold Reducing_lr_Ord. unfold Reducing_lr.
  f_equal. f_equal. f_equal.
  simpl. destruct(Oplus_term x) eqn:H1; destruct(Oplus_term y) eqn:H2; auto.
  - now rewrite app_assoc.
  - apply term_to_lTerm_Oplus in H2. rewrite H2. now rewrite app_nil_r.
  - apply term_to_lTerm_Oplus in H1. rewrite H1. rewrite app_nil_r. simpl. 
    now rewrite app_nil_r.
  - apply term_to_lTerm_Oplus in H1. apply term_to_lTerm_Oplus in H2.
    rewrite H1. rewrite H2. now rewrite app_nil_r.
Qed.

Lemma sort_NReducing_cons_dec:forall(tl:list term)(t:term),
  sort_term (NReducing(t::tl)) = sort_term(t::(NReducing tl))
  \/sort_term (NReducing(t::tl)) = sort_term(remove t (NReducing tl)). 
Proof.
  intros. unfold NReducing. assert(H:=count_NReducing'_1_0 (t::tl) t).
  simpl. destruct (Even_Odd_dec (count_occ term_beq_syn_dec tl t)).
  - apply NReducing'_notIn in e. apply n_add_not_In in e. rewrite e. 
    left. f_equal. now rewrite rev_tail.
  - apply NReducing'_In in o. right. apply n_add_In in o. rewrite o. apply rev_remove.
Qed.

Lemma insert_nat_0:forall(l:list nat),
insert_nat 0 l= 0::l.
Proof.
  intros. induction l;simpl;auto.
Qed.

Lemma sort_constterm_cons_T0:forall(l:list term),
  (sort_constterm (T0 :: l)) = T0 :: sort_constterm l.
Proof.
  intros. unfold sort_constterm. simpl. rewrite insert_nat_0. simpl. 
  auto.
Qed.

Lemma sort_varterm_cons_T0:forall(l:list term),
  (sort_varterm (T0 :: l)) = sort_varterm l.
Proof.
  intros. unfold sort_varterm. simpl. auto.
Qed.

Lemma UReducing_filterT0: forall(l:list term),
  UReducing l = filter (fun v => negb (term_beq_syn T0 v)) l.
Proof.
  intros. induction l. auto. simpl UReducing. 
  assert(H1:=filter_app (fun v : term => negb (term_beq_syn T0 v)) [a] l). 
  simpl app in H1 at 1.
  rewrite H1. rewrite <- IHl. destruct (term_beq_syn T0 a)eqn:H2.
  - apply term_beq_syn_true_iff in H2. rewrite H2. simpl. 
    rewrite term_beq_syn_relf. auto.
  - rewrite term_beq_syn_sym in H2. rewrite H2. 
    rewrite term_beq_syn_sym in H2. simpl. destruct a;auto.
    destruct n;auto. apply term_beq_syn_false_iff in H2. exfalso.
    now apply H2.
Qed.

Definition Const_term(t:term):bool:=
  match t with
  |C _ => true
  |_ => false
  end.

Definition Var_term(t:term):bool:=
  match t with
  |V _ => true
  |_ => false
  end.

Definition filter0 l:list nat:=
  filter (fun n => negb ( NatUtil.beq_nat n 0 )) l.


Lemma lntlc_lctln_UReducing:forall(l:list term),
  UReducing(list_nat_to_list_const(list_const_to_list_nat l))
  = (list_nat_to_list_const(list_const_to_list_nat (UReducing l))).
Proof.
  intros. induction l. auto. simpl.
  destruct a.
  - simpl. destruct(NatUtil.beq_nat n 0). auto. simpl. now f_equal.
  - auto.
  - auto.
Qed.


Lemma filter0_UReducing_ln:forall (l:list nat),
  list_nat_to_list_const( filter0 l) = UReducing (list_nat_to_list_const l).
Proof.
  intros. induction l. auto. simpl. destruct (NatUtil.beq_nat a 0);simpl. auto.
  now f_equal.
Qed.

Lemma filter0_UReducing_lt:forall (l:list term),
  filter0 (list_const_to_list_nat l) = list_const_to_list_nat (UReducing l).
Proof.
  intros. induction l. auto. destruct a;simpl;auto. 
  destruct (NatUtil.beq_nat n 0);simpl. auto.
  now f_equal.
Qed.


Lemma filter0_insert_eq0:forall(n:nat)(l:list nat),
  NatUtil.beq_nat n 0 = true -> 
    filter0 (insert_nat n l) = (filter0 l).
Proof.
  intros. induction l.
  - simpl. rewrite H. auto.
  - simpl. destruct (n <=? a)eqn:Hna; 
    destruct(NatUtil.beq_nat a 0)eqn:Ha;simpl;rewrite Ha;simpl. 
    + rewrite H. simpl. auto.
    + rewrite H. simpl. auto.
    + auto.
    + now f_equal. 
Qed.

Lemma filter0_insert_neq0:forall(n:nat)(l:list nat),
  NatUtil.beq_nat n 0 = false -> 
    filter0 (insert_nat n l) = insert_nat n (filter0 l).
Proof.
  intros. induction l. simpl. rewrite H. auto.
  simpl. destruct (n <=? a) eqn:Hna.
  - destruct (NatUtil.beq_nat a 0) eqn:Ha;simpl; rewrite H;simpl; rewrite Ha;simpl.
    + apply NatUtil.beq_nat_ok in Ha. rewrite Ha in Hna. assert (n = 0). 
      apply Nat.leb_le in Hna. lia. rewrite H0. rewrite insert_nat_0. auto.
    + rewrite Hna. auto.
  - simpl. destruct(NatUtil.beq_nat a 0) eqn:Ha;simpl.
    + auto.
    + rewrite Hna. now f_equal.
Qed.

Lemma filter0_sort:forall(l:list nat),
    filter0 (sort_nat l) = sort_nat (filter0 l).
Proof.
  intros. induction l. auto.
  simpl. destruct(NatUtil.beq_nat a 0)eqn:Ha;simpl.
  - apply (filter0_insert_eq0 a (sort_nat l)) in Ha. rewrite Ha. auto.
  - apply (filter0_insert_neq0 a (sort_nat l)) in Ha. auto. rewrite Ha.
    now f_equal.
Qed.


Lemma UReducing_sort_constterm_homo: forall(l:list term),
  UReducing (sort_constterm l) = sort_constterm (UReducing l).
Proof.
  intros. unfold sort_constterm.
  induction l. auto. destruct a;auto.
  simpl. destruct (NatUtil.beq_nat n 0) eqn:H1.
  - assert(J:=insert_nat_exists n(sort_nat (list_const_to_list_nat l))).
    destruct J. destruct H. destruct H.
    rewrite H. unfold list_nat_to_list_const. rewrite map_app. 
    rewrite UReducing_app. rewrite map_cons. simpl.
    rewrite H1. rewrite <- UReducing_app. auto. rewrite <- map_app. rewrite H0. auto.
  - simpl. rewrite <- filter0_UReducing_ln. f_equal. 
    apply (filter0_insert_neq0 _ (sort_nat (list_const_to_list_nat l))) in H1.
    rewrite H1. f_equal. rewrite filter0_sort. f_equal. apply filter0_UReducing_lt.
Qed. 


Lemma lvtlv_UReducing:forall(l:list term),
  list_Var_to_list_var l = list_Var_to_list_var (UReducing l).
Proof.
  intros. induction l. auto. destruct a;simpl;auto.
  destruct(NatUtil.beq_nat n 0 );auto. now f_equal.
Qed.

Lemma UReducing_lvtlv:forall(l:list var),
  list_var_to_list_Var l = UReducing(list_var_to_list_Var l).
Proof.
  intros. induction l. auto. simpl. now f_equal.
Qed.
  

Lemma UReducing_sort_varterm_homo: forall(l:list term),
  UReducing (sort_varterm l) = sort_varterm (UReducing l).
Proof.
  intros. induction l.
  - simpl. unfold sort_varterm. auto.
  - unfold sort_varterm. destruct a eqn:Ha;simpl;auto. destruct (NatUtil.beq_nat n 0 );auto.
    rewrite lvtlv_UReducing. rewrite <- UReducing_lvtlv. auto.
Qed.

Lemma UReducing_sort_term_homo: forall(l:list term),
  UReducing (sort_term l) = sort_term (UReducing l).
Proof.
  intros. unfold sort_term. rewrite UReducing_app.
  rewrite UReducing_sort_constterm_homo.
  rewrite UReducing_sort_varterm_homo.
  auto.
Qed.


Lemma ltSorted_Permutation:forall(l1 l2:list term),
  AReduced l1 -> AReduced l2 ->
  ltSorted l1 -> ltSorted l2 -> Permutation l1 l2 -> l1 = l2.
Proof.
  intros. apply ltSorted_sort_term in H;auto. apply ltSorted_sort_term in H0;auto.
  rewrite <- H. rewrite <- H0. apply Permutation_sort_same. auto.
Qed.

Lemma Permutation_AReduced:forall(l1 l2:list term),
  Permutation l1 l2 -> AReduced l1 -> AReduced l2.
Proof.
  intros. induction H.
  - constructor.
  - inversion H0;subst;firstorder. constructor. auto. constructor. auto.
  - inversion H0; subst; inversion H1; subst; repeat(constructor;auto).
  - firstorder.
Qed.

Lemma Permutation_NReduced:forall(l1 l2:list term),
  Permutation l1 l2 -> NReduced l1 -> NReduced l2.
Proof.
  intros. induction H.
  - constructor.
  - inversion H0;subst;firstorder. constructor. 
    assert(J1:=Permutation_Not_In l l' (C n) H H3). auto. auto. constructor; auto.
    now assert(J1:=Permutation_Not_In l l' (V v) H H3).
  - inversion H0; subst. inversion H3; subst. constructor. apply not_in_cons.
    split;auto. apply not_in_cons in H2. destruct H2. now apply not_eq_sym in H.
    constructor. apply not_in_cons in H2. now destruct H2. auto.
    constructor. apply not_in_cons. split;auto. intro. inversion H.
    constructor; auto. apply not_in_cons in H2. now destruct H2.
    inversion H3;subst. constructor. apply not_in_cons. split;auto. now intro.
    constructor. now apply not_in_cons in H2. auto. constructor.
    apply not_in_cons. apply not_in_cons in H2. destruct H2. split;auto.
    constructor. now apply not_in_cons in H2. auto.
  - firstorder.
Qed.

Lemma sort_term_nil: 
  sort_term [] = [].
Proof.
  auto.
Qed. 

Lemma sort_AReduced:forall(l:list term),
  AReduced l -> AReduced (sort_term l).
Proof.
  intros. induction H. 
  - rewrite sort_term_nil. constructor.
  - assert(AReduced (C n :: tl)). now constructor.
    assert(H1:=sort_ltSorted_Permutation ((C n) :: tl) H0). 
    apply Permutation_AReduced in H1;auto.
  - assert(AReduced (V v :: tl)). now constructor.
    assert(H1:=sort_ltSorted_Permutation ((V v) :: tl) H0). 
    apply Permutation_AReduced in H1;auto.
Qed.



Lemma sort_term_idpt:forall(tl:list term),
  AReduced tl -> sort_term tl = sort_term (sort_term tl).
Proof.
  intros. assert(H1:=sort_ltSorted tl).
  apply sort_AReduced in H.
  apply ltSorted_sort_term in H;auto.
Qed.

Lemma Reduced_Reducing: forall(tl:list term),
  Reduced tl -> Reducing_lr tl = tl.
Proof.
  intros. inversion H;subst. unfold Reducing_lr.
  rewrite AReduced_AReducing_idpt;auto. rewrite NReduced_NReducing;auto.
  rewrite UReduced_UReducing;auto.
Qed.

Lemma Reducing_lr_idpt: forall(tl:list term),
  Reducing_lr tl = Reducing_lr (Reducing_lr tl).
Proof.
  intros. 
  assert(H:=Reducing_lr_Correct_Reduced tl). inversion H;subst.
  remember (Reducing_lr tl) as rtl. unfold Reducing_lr.
  rewrite AReduced_AReducing_idpt;auto. rewrite NReduced_NReducing;auto.
  rewrite UReduced_UReducing;auto.
Qed.

Lemma Reducing_lr_Ord_Reducing_lr:forall(tl:list term),
  Reducing_lr_Ord tl = Reducing_lr_Ord (Reducing_lr tl).
Proof.
  intros. unfold Reducing_lr_Ord at 1. 
  assert(H:=Reducing_lr_Correct_Reduced tl). inversion H;subst.
  remember (Reducing_lr tl) as rtl. unfold Reducing_lr_Ord.
  apply Reduced_Reducing in H. rewrite H. auto.
Qed.


Lemma Permutation_cons_app : forall (l l1 l2:list term) a,
  Permutation l (l1 ++ l2) -> Permutation (a :: l) (l1 ++ a :: l2).
Proof.
  intros. assert(Permutation (a::l)(a::l1++l2)).
  - now constructor.
  - rewrite H0. cut (Permutation (a::l1)(l1++[a]));intros. 
    apply (Permutation_app_tail l2) in H1. rewrite <- app_assoc in H1. simpl in H1. auto.
    apply Permutation_cons_append. 
Qed.

Lemma count_occ_Permutation (l1 l2:list term) :
  Permutation l1 l2 <-> forall t, count_occ term_beq_syn_dec l1 t = count_occ term_beq_syn_dec l2 t.
Proof.
  split.
  - induction 1 as [ | y l1 l2 HP IHP | y z l | l1 l2 l3 HP1 IHP1 HP2 IHP2 ];
      cbn; intros a; auto.
    + now rewrite IHP.
    + destruct (term_beq_syn_dec y a); destruct (term_beq_syn_dec z a); auto.
    + now rewrite IHP1, IHP2.
  - revert l2; induction l1 as [|y l1 IHl1]; cbn; intros l2 Hocc.
    + replace l2 with (@nil term). constructor.
      symmetry; apply (count_occ_inv_nil term_beq_syn_dec); intuition.
    + assert (exists l2' l2'', l2 = l2' ++ y :: l2'') as [l2' [l2'' ->]].
      { specialize (Hocc y).
        destruct (term_beq_syn_dec y y); intuition.
        apply in_split, (count_occ_In term_beq_syn_dec).
        rewrite <- Hocc; apply Nat.lt_0_succ. }
      assert(K:= Permutation_cons_app).
      apply Permutation_cons_app, IHl1.
      intros z; specialize (Hocc z); destruct (term_beq_syn_dec y z) as [Heq | Hneq].
      * rewrite (count_occ_elt_eq _ _ _ Heq) in Hocc.
        now injection Hocc.
      * now rewrite (count_occ_elt_neq _ _ _ Hneq) in Hocc.
Qed. 

Lemma count_occ_NReducing'_even_0:forall(t:term)(l:list term),
Nat.Even (count_occ term_beq_syn_dec l t)
<-> 
(count_occ term_beq_syn_dec (NReducing' l) t) = 0.
Proof.
  split; intros. 
  - apply NReducing'_notIn in H. now apply count_occ_not_In.
  - destruct(Even_Odd_dec (count_occ term_beq_syn_dec l t)). auto.
    apply NReducing'_In in o. apply (count_occ_In term_beq_syn_dec) in o. lia.
Qed.

Lemma count_occ_NReducing'_Odd_1:forall(t:term)(l:list term),
Nat.Odd (count_occ term_beq_syn_dec l t)
<-> 
(count_occ term_beq_syn_dec (NReducing' l) t) = 1.
Proof.
  split; intros. 
  - apply NReducing'_In in H as H0. assert(H1:=count_NReducing'_1_0 l t).
    destruct(Even_Odd_dec (count_occ term_beq_syn_dec l t)).
    + inversion H. inversion e. lia.
    + auto. 
  - assert(H1:=count_NReducing'_1_0 l t). 
    destruct(Even_Odd_dec (count_occ term_beq_syn_dec l t)).
    + lia. + auto.  
Qed.

Lemma Even_decrease:forall (n:nat),
  Nat.Even (S (S n)) -> Nat.Even n.
Proof.
  intros. destruct H. exists (x-1). lia.
Qed.

Lemma Even_add_Even_invl:
  forall n m : nat, Nat.Even (n + m) -> Nat.Even m -> Nat.Even n.
Proof.
  intros. destruct H0. rewrite H0 in H. clear H0. induction x. simpl in H.
  assert(n+0=n). lia. now rewrite H0 in H. assert(n+2*S x = S(S(n+2*x))). lia.
  rewrite H0 in H. apply Even_decrease in H. auto.
Qed.

Lemma Even_add_Odd_invl:
  forall n m : nat, Nat.Even (n + m) -> Nat.Odd m -> Nat.Odd n.
Proof.
  intros. destruct H0. rewrite H0 in H. clear H0. induction x. simpl in H.
  destruct H. exists (x-1). lia. assert(n+(2*S x +1)=S(S(n+(2*x+1)))). lia.
  rewrite H0 in H. apply Even_decrease in H. auto.
Qed.

Lemma Nat_Even_Even_add:
  forall n m : nat, Nat.Even n -> Nat.Even m -> Nat.Even (n + m).
Proof.
  intros. destruct H. destruct H0. subst. assert(2 * x + 2 * x0 = 2 * (x + x0)).
  lia. rewrite H. now exists (x + x0).
Qed.


Lemma Nat_Odd_Odd_add: 
  forall n m : nat, Nat.Odd n -> Nat.Odd m -> Nat.Even (n + m).
Proof.
  intros. destruct H. destruct H0. rewrite H. rewrite H0.
  exists (x + x0 + 1). lia.
Qed.

Lemma Nat_Odd_add_Odd_inv_r: 
  forall n m : nat, Nat.Odd (n + m) -> Nat.Even n -> Nat.Odd m.
Proof.
  intros. destruct H. destruct H0. rewrite H0 in H. 
  exists ((x - x0)). lia.
Qed.

Lemma Nat_Odd_add_Even_inv_r: 
  forall n m : nat, Nat.Odd (n + m) -> Nat.Odd n -> Nat.Even m.
Proof.
  intros. destruct H. destruct H0. rewrite H0 in H.
  exists (x - x0). lia.
Qed.

Lemma Nat_Odd_add_r:
  forall n m : nat, Nat.Even n -> Nat.Odd m -> Nat.Odd (n + m).
Proof.
  intros. destruct H. destruct H0. exists (x+x0). lia.
Qed.

Lemma Nat_Odd_add_l: 
  forall n m : nat, Nat.Odd n -> Nat.Even m -> Nat.Odd (n + m).
Proof.
  intros. destruct H. destruct H0. exists (x + x0). lia.
Qed.


Definition count_occ_rev_eq: 
  forall (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y})
         (l : list A) (x : A),
       count_occ eq_dec (rev l) x = count_occ eq_dec l x.
Proof.
  intros. induction l. auto. simpl. rewrite count_occ_app. simpl.
  destruct (eq_dec a x);lia.
Qed.



Lemma sort_NReducing_whithin_l: forall(l1 l2:list term),
  AReduced l1 -> AReduced l2 -> 
  sort_term(NReducing (l1++l2)) = sort_term(NReducing ((NReducing l1)++l2)).
Proof.
  intros. unfold NReducing. rewrite sort_rev. rewrite sort_rev.
  apply Permutation_sort_same. apply count_occ_Permutation.
  intros. 
  assert(H1:=count_NReducing'_1_0 (l1 ++ l2) t). 
  destruct(Even_Odd_dec (count_occ term_beq_syn_dec (l1 ++ l2) t)).
  - rewrite H1. symmetry. apply count_occ_NReducing'_even_0.
    rewrite (count_occ_app term_beq_syn_dec) in *. 
    destruct (Even_Odd_dec (count_occ term_beq_syn_dec l2 t)).
    -- assert(J:=Even_add_Even_invl _ _ e e0).
       apply Nat_Even_Even_add;auto. rewrite (count_occ_rev_eq).
       apply count_occ_NReducing'_even_0 in J. rewrite J. now exists 0.
    -- assert(J:=Even_add_Odd_invl _ _ e o). apply Nat_Odd_Odd_add;auto.
       rewrite count_occ_rev_eq. apply count_occ_NReducing'_Odd_1 in J. rewrite J.
       now exists 0.
  - rewrite H1. symmetry. apply count_occ_NReducing'_Odd_1.
    rewrite (count_occ_app term_beq_syn_dec) in *. 
    destruct (Even_Odd_dec (count_occ term_beq_syn_dec l1 t)).
    -- apply Nat_Odd_add_Odd_inv_r in o;auto. apply Nat_Odd_add_r; auto.
       rewrite (count_occ_rev_eq). 
       apply count_occ_NReducing'_even_0 in e. rewrite e. now exists 0.
    -- assert(J:=Nat_Odd_add_Even_inv_r _ _ o o0). apply Nat_Odd_add_l; auto.
       rewrite (count_occ_rev_eq). 
       apply count_occ_NReducing'_Odd_1 in o0. rewrite o0. now exists 0.
Qed.


Lemma Even_add_Even_invr:
  forall n m : nat, Nat.Even (n + m) -> Nat.Even n -> Nat.Even m.
Proof.
  intros. destruct H0. rewrite H0 in H. clear H0. induction x. now simpl in H.
  assert(2*S x+m = S(S(2*x+m))). lia.
  rewrite H0 in H. apply Even_decrease in H. auto.
Qed.

Lemma Even_add_Odd_invr:
  forall n m : nat, Nat.Even (n + m) -> Nat.Odd n -> Nat.Odd m.
Proof.
  intros. destruct H0. rewrite H0 in H. clear H0. induction x. simpl in H. 
  destruct H. exists (x-1). lia. assert((2*S x +1)+m=S(S((2*x+1)+m))). lia.
  rewrite H0 in H. apply Even_decrease in H. auto.
Qed.


Lemma sort_NReducing_whithin_r: forall(l1 l2:list term),
  AReduced l1 -> AReduced l2 -> 
  sort_term(NReducing (l1++l2)) = sort_term(NReducing (l1++(NReducing l2))).
Proof.
  intros. unfold NReducing. rewrite sort_rev. rewrite sort_rev.
  apply Permutation_sort_same. apply count_occ_Permutation.
  intros. 
  assert(H1:=count_NReducing'_1_0 (l1 ++ l2) t). destruct(Even_Odd_dec (count_occ term_beq_syn_dec (l1 ++ l2) t)).
  - rewrite H1. symmetry. apply count_occ_NReducing'_even_0.
    rewrite (count_occ_app term_beq_syn_dec) in *. 
    destruct (Even_Odd_dec (count_occ term_beq_syn_dec l1 t)).
    -- assert(J:=Even_add_Even_invr _ _ e e0). 
       assert(J1:=Nat_Even_Even_add (count_occ term_beq_syn_dec l1 t) 
       (count_occ term_beq_syn_dec (rev (NReducing' l2)) t) e0). apply J1.
       clear e H1 e0 J1. assert(H1:=count_occ_rev_eq).
       rewrite H1. apply count_occ_NReducing'_even_0 in J. rewrite J. exists 0. auto.
    -- assert(J:=Even_add_Odd_invr _ _ e o). apply Nat_Odd_Odd_add;auto.
       rewrite count_occ_rev_eq. apply count_occ_NReducing'_Odd_1 in J. rewrite J.
       now exists 0.
  - rewrite H1. symmetry. apply count_occ_NReducing'_Odd_1.
    rewrite (count_occ_app term_beq_syn_dec) in *. 
    destruct (Even_Odd_dec (count_occ term_beq_syn_dec l1 t)).
    -- apply Nat_Odd_add_Odd_inv_r in o;auto. apply Nat_Odd_add_r; auto.
       rewrite (count_occ_rev_eq). 
       apply count_occ_NReducing'_Odd_1 in o. rewrite o. now exists 0.
    -- assert(J:=Nat_Odd_add_Even_inv_r _ _ o o0). apply Nat_Odd_add_l; auto.
       rewrite (count_occ_rev_eq). 
       apply count_occ_NReducing'_even_0 in J. rewrite J. now exists 0.
Qed.

(*   
  assert(AReduced (l1++l2)). now apply AReduced_app.
  assert(AReduced (NReducing (l1 ++ l2))). now apply AReducing_NReducing_AReduced_list.
  apply AReducing_NReducing_AReduced_list in H0 as H3. 
  assert(AReduced (l1 ++ (NReducing l2))). now apply AReduced_app.
  apply AReducing_NReducing_AReduced_list in H4.
  assert(J1:=sort_Permutation_same (NReducing (l1 ++ l2)) (NReducing (l1 ++ NReducing l2)) H2 H4). *)


Lemma UReducing_remove_T0:forall(l:list term),
  UReducing (remove T0 l) = UReducing l.
Proof.
  intros. induction l. auto.
  simpl. destruct (term_beq_syn a T0) eqn:H. auto. simpl. rewrite H.
  now f_equal.
Qed.

Lemma neq_not_In_remove: forall(a t:term)(l:list term),
  a <> t -> ~ In t (remove a l) -> ~ In t l.
Proof.
  intros. induction l. auto. simpl in *. destruct (term_beq_syn a0 a) eqn:H1.
  - apply term_beq_syn_true_iff in H1. rewrite H1 in *. intro. destruct H2.
    now apply H in H2. now apply H0 in H2.
  - intro. apply not_in_cons in H0. destruct H0. destruct H2. symmetry in H2.
    now apply H0 in H2. firstorder. 
Qed.

Lemma not_In_remove_dec:forall(a t:term)(l:list term),
  ~ In t (remove a l) -> ~ In t l \/ a = t.
Proof.
  intros. destruct (In_dec a l).
  - destruct (term_beq_syn a t) eqn:H1. apply term_beq_syn_true_iff in H1. now right.
    left. apply neq_not_In_remove with a. now apply term_beq_syn_false_iff in H1. auto.
  - apply remove_noop in n. rewrite n in H. now left.
Qed.


Lemma UReducing_incl:forall(l:list term),
  incl (UReducing l) l.
Proof.
  intros. induction l;simpl. apply incl_refl.
  destruct(term_beq_syn a T0).
  - assert(H:=incl_tran). apply H with l. auto. unfold incl. intro. simpl. now right.
  - unfold incl in *. intros. inversion H. now left. apply IHl in H0. now right.
Qed.


Lemma In_remove_count_occ:forall(t:term)(l:list term),
  In t (remove t l) -> le 2 (count_occ term_beq_syn_dec l t).
Proof.
  intros. induction l. inversion H. simpl in *.
  destruct (term_beq_syn_dec a t).
  - rewrite e in H. rewrite term_beq_syn_relf in H. assert(1 <= (count_occ term_beq_syn_dec l t)).
    + assert(H1:=count_occ_In term_beq_syn_dec l t). apply H1 in H. lia.
    + lia.
  - apply term_beq_syn_false_iff in n as n2. rewrite n2 in H. inversion H. now apply n in H0.
    apply IHl in H0. lia.
Qed.

Lemma count_occ_nadd_fequal:forall (t:term)(l1 l2:list term),
(List.count_occ term_beq_syn_dec l1 t) = (List.count_occ term_beq_syn_dec l2 t)
->
(List.count_occ term_beq_syn_dec (n_add t l1) t) = (List.count_occ term_beq_syn_dec (n_add t l2) t).
Proof.
  intros. assert(H1:=count_n_add l1 t t). assert(H2:=count_n_add l2 t t).
  rewrite H in *. destruct(term_beq_syn_dec t t).
  - destruct(count_occ term_beq_syn_dec l2 t);congruence.
  - destruct(count_occ term_beq_syn_dec l2 t);congruence.
Qed.

Lemma count_occ_NUReducing:forall(t:term)(l:list term),
  t <> T0 -> 
  (List.count_occ term_beq_syn_dec (NReducing' l) t) = 
  (List.count_occ term_beq_syn_dec (NReducing' (UReducing l)) t).
Proof.
  intros. induction l. auto. simpl. destruct(term_beq_syn a t) eqn:H1.
  - apply term_beq_syn_true_iff in H1 as H2. rewrite <- H2 in H. apply term_beq_syn_false_iff in H as H3.
    rewrite H3. simpl. rewrite H2. now apply count_occ_nadd_fequal.
  - destruct(term_beq_syn a T0)eqn:H2.
    + rewrite <- IHl. destruct(In_dec a (NReducing' l)). 
      -- apply term_beq_syn_false_iff in H1. 
         apply (n_add_neq_count _ _ (NReducing' l)) in H1. auto.
      -- apply n_add_not_In in n. rewrite n. rewrite (count_occ_app term_beq_syn_dec). simpl.
         destruct (term_beq_syn_dec a t). rewrite e in H1. now rewrite term_beq_syn_relf in H1. auto.
    + simpl. apply term_beq_syn_false_iff in H1. 
      apply (n_add_neq_count _ _ (NReducing' l)) in H1 as J1.
      apply (n_add_neq_count _ _ (NReducing' (UReducing l))) in H1. congruence.
Qed.

Lemma In_NReducing'_UReducing: forall(t:term)(l:list term),
  t <> T0 -> In t (NReducing' l) -> In t (NReducing' (UReducing l)).
Proof.
  intros. apply (count_occ_NUReducing t l) in H.
  apply (count_occ_In term_beq_syn_dec) in H0. apply (count_occ_In term_beq_syn_dec). lia.
Qed.

Lemma neq_In_remove: forall(t1 t2:term)(l:list term),
  t1 <> t2 -> In t1 l <-> In t1 (remove t2 l).
Proof.
  split; intros;simpl in *.
  - induction l. inversion H0. simpl. destruct (term_beq_syn a t2) eqn:H1.
    inversion H0. apply term_beq_syn_true_iff in H1. rewrite <- H2 in H. now apply H in H1.
    auto. inversion H0. now left. apply IHl in H2. now right.
  - induction l. inversion H0. simpl in H0. destruct (term_beq_syn a t2) eqn:H1. 
    now right. inversion H0. now left. apply IHl in H2. now right.
Qed.

Lemma In_UReducing_not_T0:forall(t:term)(l:list term),
  In t (NReducing' (UReducing l)) -> t <> T0.
Proof.
  intros. induction l. inversion H. simpl in H. destruct (term_beq_syn a T0) eqn:H1.
  firstorder. destruct (In_dec a (NReducing' (UReducing l))).
  - apply n_add_In in i. simpl in H. rewrite i in H. destruct (term_beq_syn_dec a t).
    + rewrite e in H1. now apply term_beq_syn_false_iff in H1.
    + apply not_eq_sym in n. apply (neq_In_remove t a (NReducing' (UReducing l))) in n. apply n in H.
      now apply IHl in H.
  - simpl in H. apply n_add_not_In in n. rewrite n in H. apply in_app_or in H.
    destruct H. now apply IHl. inversion H. rewrite H0 in H1. now apply term_beq_syn_false_iff in H1.
    inversion H0.
Qed.


Lemma incl_NReducing_NUReducing: forall (l:list term),
  incl (NReducing' (UReducing l)) (NReducing' l).
Proof.
  intros. unfold incl. intros. destruct (term_beq_syn_dec a T0).
  - rewrite e in H. apply In_UReducing_not_T0 in H. exfalso. now apply H.
  - assert(H1:=count_occ_NUReducing a l n). apply (count_occ_In term_beq_syn_dec).
    apply (count_occ_In term_beq_syn_dec) in H. lia.
Qed.

Lemma not_In_NReducing'_UReducing: forall(t:term)(l:list term),
  ~ In t (NReducing' l) -> ~ In t (NReducing' (UReducing l)).
Proof.
  intros. assert(H1:= incl_NReducing_NUReducing). 
  intro. apply H. unfold incl in H1. auto.
Qed.

Lemma UReducing_remove_homo:forall(t:term)(l:list term),
  UReducing(remove t l) = remove t (UReducing l).
Proof.
  intros. induction l. auto. simpl. destruct(term_beq_syn a t) eqn:Hat; 
  destruct(term_beq_syn a T0) eqn:HaT0.
  - assert(H:= UReducing_remove_T0 l). rewrite <- H at 1. apply term_beq_syn_true_iff in Hat.
    apply term_beq_syn_true_iff in HaT0. rewrite HaT0 in Hat. now rewrite Hat. 
  - simpl. now rewrite Hat.
  - simpl. now rewrite HaT0.
  - simpl. rewrite Hat. rewrite HaT0. now f_equal.
Qed.

Lemma UReducing_NReducing_homo: forall(l:list term),
  AReduced l -> UReducing(NReducing l) = NReducing(UReducing l).
Proof.
  intros. induction l. auto.
  inversion H;subst;apply IHl in H1.
  - simpl. destruct (NatUtil.beq_nat n 0) eqn:H0.
    + rewrite <- H1. assert(H2:=UNReducing_T0_mid nil l). apply NatUtil.beq_nat_ok in H0. 
      rewrite H0. now simpl in H2. 
    + unfold NReducing. simpl. destruct (In_dec (C n)(NReducing' l)).
      -- apply n_add_In in i as i2. rewrite i2. cut ( (C n) <> T0).
         intro. assert(i3:= In_NReducing'_UReducing (C n) l H2 i). apply n_add_In in i3.
         rewrite UReducing_rev_homo. f_equal. rewrite i3. rewrite UReducing_remove_homo. 
         unfold NReducing in H1. rewrite UReducing_rev_homo in H1. 
         f_equal. now apply rev_f_equal in H1.
         intro. inversion H2. rewrite H4 in H0. inversion H0. 
      -- apply n_add_not_In in n0 as n1. rewrite n1. 
         apply not_In_NReducing'_UReducing in n0. apply n_add_not_In in n0. rewrite n0.
         rewrite rev_simp. rewrite rev_simp. simpl. rewrite H0. now f_equal.
  - unfold NReducing. simpl. destruct (In_dec (V v)(NReducing' l)).
      -- apply n_add_In in i as i2. rewrite i2. cut ((V v) <> T0).
         intro. assert(i3:= In_NReducing'_UReducing (V v) l H0 i). apply n_add_In in i3.
         rewrite UReducing_rev_homo. f_equal. rewrite i3. rewrite UReducing_remove_homo. 
         unfold NReducing in H1. rewrite UReducing_rev_homo in H1. 
         f_equal. now apply rev_f_equal in H1. intro. inversion H0.
      -- apply n_add_not_In in n as n1. rewrite n1. 
         apply not_In_NReducing'_UReducing in n. apply n_add_not_In in n. rewrite n.
         rewrite rev_simp. rewrite rev_simp. simpl. f_equal. auto. 
Qed.

Lemma UReducing_idpt: forall(l:list term),
  UReducing l = UReducing(UReducing l).
Proof.
  intros. induction l. auto. simpl. destruct (term_beq_syn a T0) eqn:H.
  auto. simpl. rewrite H. now f_equal.
Qed.


Lemma Reducing_lr_Ord_idpt_Reducing_l: forall(tl1 tl2:list term),
  Reducing_lr_Ord (tl1 ++ tl2) = Reducing_lr_Ord((Reducing_lr tl1) ++ tl2).
Proof.
  intros. unfold Reducing_lr_Ord. unfold Reducing_lr. 
  rewrite <- AReducing_lr_app.
  assert(ARtl1l2:=AReducing_lr_Correct_Reduced 
  (UReducing (NReducing (AReducing_lr tl1)) ++ tl2)).
  rewrite <- AReducing_lr_app in *. 
  assert(ARtl1:=AReducing_lr_Correct_Reduced tl1).
  assert(ARtl2:=AReducing_lr_Correct_Reduced tl2).
  remember (AReducing_lr tl1) as atl1. 
  remember (AReducing_lr tl2) as atl2. 
  assert(NARtl1:=AReducing_NReducing_AReduced_list _ ARtl1).
  assert(UNARtl1:=AReducing_UReducing_AReduced_list _ NARtl1).
  assert(H:=AReduced_AReducing_idpt _ UNARtl1).
  apply UReducing_NReducing_homo in ARtl1l2. 
  rewrite ARtl1l2. rewrite UReducing_app.
  rewrite H. rewrite <- UReducing_idpt. rewrite <- UReducing_app.
  assert(AReduced((NReducing atl1 ++ atl2))).
  - apply AReduced_app;auto.
  - assert(AReduced((atl1 ++ atl2))). apply AReduced_app;auto.
    apply UReducing_NReducing_homo in H1. rewrite H1. rewrite UReducing_app.
    rewrite UReducing_app. apply UReducing_NReducing_homo in ARtl1 as H2. rewrite H2.
    assert(J1:= AReducing_UReducing_AReduced_list atl1).
    assert(J2:= AReducing_UReducing_AReduced_list atl2).
    firstorder. apply sort_NReducing_whithin_l;auto.
Qed.

Lemma Reducing_lr_Ord_idpt_Reducing_r: forall(tl1 tl2:list term),
  Reducing_lr_Ord (tl1 ++ tl2) = Reducing_lr_Ord(tl1 ++ (Reducing_lr tl2)).
Proof.  
  intros. unfold Reducing_lr_Ord. unfold Reducing_lr. 
  rewrite <- AReducing_lr_app.
  assert(ARtl1l2:=AReducing_lr_Correct_Reduced 
  (tl1 ++ UReducing (NReducing (AReducing_lr tl2)))).
  rewrite <- AReducing_lr_app in *. 
  assert(ARtl1:=AReducing_lr_Correct_Reduced tl1).
  assert(ARtl2:=AReducing_lr_Correct_Reduced tl2).
  remember (AReducing_lr tl1) as atl1. 
  remember (AReducing_lr tl2) as atl2. 
  assert(NARtl2:=AReducing_NReducing_AReduced_list _ ARtl2).
  assert(UNARtl2:=AReducing_UReducing_AReduced_list _ NARtl2).
  assert(H:=AReduced_AReducing_idpt _ UNARtl2).
  apply UReducing_NReducing_homo in ARtl1l2. 
  rewrite ARtl1l2. rewrite UReducing_app.
  rewrite H. rewrite <- UReducing_idpt. rewrite <- UReducing_app.
  assert(AReduced(atl1 ++ NReducing atl2)).
  - apply AReduced_app;auto.
  - assert(AReduced((atl1 ++ atl2))). apply AReduced_app;auto.
    apply UReducing_NReducing_homo in H1. rewrite H1. rewrite UReducing_app.
    rewrite UReducing_app. apply UReducing_NReducing_homo in ARtl2 as H2. rewrite H2.
    assert(J1:= AReducing_UReducing_AReduced_list atl1).
    assert(J2:= AReducing_UReducing_AReduced_list atl2).
    firstorder. apply sort_NReducing_whithin_r;auto.
Qed.

Lemma lntlc_fequal:forall(l1 l2:list nat),
  l1 = l2 <-> list_nat_to_list_const l1 = list_nat_to_list_const l2.
Proof.
  split.
  - intros. now rewrite H.
  - unfold list_nat_to_list_const. generalize dependent l2. pattern l1. induction l1.
    + intros. simpl in H. symmetry in H. apply map_eq_nil in H. auto.
    + intros. destruct l2. simpl in H. inversion H.
      simpl in H. injection H;intros. f_equal. auto. apply IHl1. auto.
Qed.

Lemma lvtlv_fequal:forall(l1 l2:list var),
  l1 = l2 <-> list_var_to_list_Var l1 = list_var_to_list_Var l2.
Proof.
  split.
  - intros. now rewrite H.
  - unfold list_var_to_list_Var. generalize dependent l2. pattern l1. induction l1.
    + intros. simpl in H. symmetry in H. apply map_eq_nil in H. auto.
    + intros. destruct l2. simpl in H. inversion H.
      simpl in H. injection H;intros. f_equal. auto. apply IHl1. auto.
Qed.

Lemma sort_term_app_l:forall(tl1 tl2 tl3:list term),
  sort_term tl2 = sort_term tl3  ->
  sort_term(tl1 ++ tl2) = sort_term(tl1 ++ tl3).
Proof.
  intros. 
  unfold sort_term. apply sort_term_eq_const_var_eq in H. destruct H.
  apply sort_term_eq_const_var_eq. split.
  - clear H0. induction tl1. auto.
    unfold sort_constterm in *. destruct a;auto. simpl. apply lntlc_fequal in IHtl1.
    rewrite IHtl1. auto.
  - clear H. induction tl1. simpl. auto.
    unfold sort_varterm in *. destruct a;auto. simpl. apply lvtlv_fequal in IHtl1.
    rewrite IHtl1. auto.
Qed.

Lemma sort_term_app_r:forall(tl1 tl2 tl3:list term),
  sort_term tl2 = sort_term tl3 ->
  sort_term(tl2 ++ tl1) = sort_term(tl3 ++ tl1).
Proof.
  intros. rewrite sort_comm. apply (sort_term_app_l tl1)in H.
  rewrite H. apply sort_comm.
Qed.


Lemma sort_term_within_l:forall(tl1 tl2:list term),
  AReduced tl1 -> sort_term (tl1 ++ tl2) = sort_term((sort_term tl1) ++ tl2).
Proof.
  intros. apply sort_term_app_r. rewrite <- sort_term_idpt;auto.
Qed.

Lemma sort_term_within_r:forall(tl1 tl2:list term),
  AReduced tl2 -> sort_term (tl1 ++ tl2) = sort_term(tl1 ++ (sort_term tl2)).
Proof.
  intros. apply sort_term_app_l. rewrite <- sort_term_idpt;auto.
Qed.

Lemma Rvc_Refl:forall(t:term),
  AReduced [t] -> Rvc t t.
Proof.
  intros. destruct t; try constructor;auto.
  unfold order_string. now rewrite compare_refl. inversion H.
Qed.

Lemma Rvc_trans:forall(t1 t2 t3:term),
  Rvc t1 t2 -> Rvc t2 t3 -> Rvc t1 t3.
Proof.
  intros. inversion H;subst;inversion H0;subst.
  - constructor. apply order_string_tran with v2;auto.
  - constructor.
  - constructor.
  - constructor. lia.
Qed.

Lemma ltSorted_forall_Rvc_smallest:forall(t:term)(l:list term),
  ltSorted(t::l) -> (forall t', In t' l -> Rvc t t').
Proof.
  intros. apply ltSorted_remove in H as H1. induction H1.
  - inversion H0.
  - destruct H0. rewrite H0 in H. inversion H;subst. auto. inversion H0.
  - inversion H0. rewrite H3 in *. inversion H;subst. auto.
    apply IHltSorted;auto.  apply ltSorted_skip in H. auto.
Qed.

Lemma ltSorted_cons_forall_Rvc_smallest:forall(t:term)(l:list term),
  ltSorted l -> (forall t', In t' l -> Rvc t t') -> ltSorted (t::l).
Proof.
  intros. induction H.
  - constructor.
  - constructor. constructor. apply (H0 a). auto. now left.
  - assert(H2:=H0 a). constructor.
    + constructor;auto.
    + apply H2. now left.
Qed.

Lemma ltSorted_front_back: forall(t1 t2:term)(l:list term),
  ltSorted(t1 :: l ++ [t2]) -> Rvc t1 t2.
Proof.
  intros. induction l.
  - simpl in H. inversion H;subst. auto.
  - simpl in H. apply ltSorted_skip in H. auto.
Qed.

Lemma ltSorted_front_middle: forall(t1 t2:term)(l1 l2:list term),
  ltSorted(t1 :: l1 ++ [t2] ++ l2) -> Rvc t1 t2.
Proof.
  intros. induction l1.
  - simpl in H. inversion H;subst. auto.
  - simpl in H. apply ltSorted_skip in H. auto.
Qed.


Lemma ltSorted_break:forall(l1 l2:list term),
  ltSorted(l1 ++ l2) -> ltSorted l1 /\ ltSorted l2.
Proof.
  split;intros.
  - induction l1. constructor. simpl in *. apply ltSorted_cons_forall_Rvc_smallest.
    + apply ltSorted_remove in H. auto.
    + intros. assert(K:=ListUtil.in_elim H0). destruct K. destruct H1. rewrite H1 in H.
      assert((a :: (x ++ t' :: x0) ++ l2) = a :: x ++ [t'] ++ (x0 ++ l2)).
      {simpl. f_equal. rewrite <- app_assoc. f_equal. }
      rewrite H2 in H. assert(J2:=ltSorted_front_middle a t' _ _ H). auto.
  - induction l1. auto. simpl in H. apply ltSorted_remove in H. auto.
Qed.



Lemma ltSorted_forall_Rvc_biggest:forall(t:term)(l:list term),
  ltSorted(l++[t]) -> (forall t', In t' l -> Rvc t' t).
Proof.
  intros. apply ltSorted_break in H as H1. destruct H1.
  induction H1.
  - inversion H0.
  - destruct H0. rewrite H0 in H. inversion H;subst. auto. inversion H0.
  - simpl in *. inversion H0. 
    + subst. apply (ltSorted_front_back _ _ (b::l)) in H. auto.
    + apply IHltSorted. simpl in *. apply ltSorted_remove in H. auto. auto. 
Qed.

Lemma ltSorted_cons_forall_Rvc_biggest:forall(t:term)(l:list term),
  ltSorted l -> (forall t', In t' l -> Rvc t' t) -> ltSorted (l++[t]).
Proof.
  intros. induction H.
  - constructor.
  - constructor. constructor. apply (H0 a). auto. now left.
  - simpl. constructor;auto.
    simpl in IHltSorted. apply IHltSorted. intros. destruct H2.
    + apply H0. rewrite H2. right. now left.
    + apply H0. right. right. auto.
Qed.

Lemma ltSorted_rev_remove:forall(t:term)(l:list term),
  ltSorted(rev l) -> ltSorted (rev (remove t l)).
Proof.
  intros. induction l;simpl. constructor.
  destruct(term_beq_syn a t)eqn:Hat. simpl in H. apply ltSorted_break in H. destruct H.
  auto. simpl. simpl in H. apply ltSorted_break in H as H1. destruct H1.
  apply IHl in H0. apply ltSorted_cons_forall_Rvc_biggest. apply ltSorted_break in H. destruct H.
  auto. intros. assert(J:=ltSorted_forall_Rvc_biggest a (rev l) H t'). apply J.
  apply ListUtil.in_rev. apply in_rev in H2. assert(J2:=remove_incl t l).
  unfold incl in J2. apply (J2 t'). auto.
Qed.




Lemma incl_NReducing':forall(l:list term),
  incl (NReducing' l) l.
Proof.
  intros. unfold incl. intros. induction l. auto.
  simpl in H. destruct(In_dec a0 (NReducing' l)).
  - apply n_add_In in i. rewrite i in H. destruct(term_beq_syn a a0) eqn:Haa0.
    + apply term_beq_syn_true_iff in Haa0. rewrite Haa0. now left.
    + apply term_beq_syn_false_iff in Haa0. 
      apply (neq_In_remove _ _(NReducing' l)) in Haa0. apply Haa0 in H. right. auto.
  - apply n_add_not_In in n. rewrite n in H. apply in_app_or in H. destruct H.
    + right. auto.
    + inversion H. now left. inversion H0.
Qed.

Lemma ltSorted_NReducing:forall(l:list term),
  AReduced l -> ltSorted l -> ltSorted (NReducing l).
Proof.
  intros. induction H0;simpl;try constructor. remember (b::l).
  unfold NReducing in *. simpl in *. subst. 
  destruct (In_dec a (NReducing' (b :: l))).
  - apply n_add_In in i. rewrite i. apply ltSorted_rev_remove. 
    inversion H;subst;apply IHltSorted in H3;auto.
  - apply n_add_not_In in n. rewrite n. rewrite rev_simp. 
    apply ltSorted_cons_forall_Rvc_smallest. inversion H;subst; apply IHltSorted in H3;auto.
    intros. assert(J:=ltSorted_forall_Rvc_smallest b l H0 t'). 
    assert(incl (rev(NReducing' (b::l))) (b::l)).
    {assert(L:=incl_NReducing' (b::l)). assert(L1:=ListUtil.rev_incl (NReducing'(b::l))).
     assert(J1:=incl_tran L1 L). auto. }
    unfold incl in H3. assert(H4:=H3 t'). apply H4 in H2. inversion H2.
    -- rewrite H5 in *. auto.
    -- apply Rvc_trans with b;auto.
Qed.

Lemma AReduced_NReducing':forall(l:list term),
  AReduced l -> AReduced(NReducing' l).
Proof.
  intros. induction H;simpl.
  - constructor.
  - destruct(In_dec (C n) (NReducing' tl)).
    + apply n_add_In in i. rewrite i. apply AReduced_remove. auto.
    + apply n_add_not_In in n0. rewrite n0. apply AReduced_app;auto. repeat constructor. 
  - destruct(In_dec (V v) (NReducing' tl)).
    + apply n_add_In in i. rewrite i. apply AReduced_remove. auto.
    + apply n_add_not_In in n. rewrite n. apply AReduced_app;auto. repeat constructor. 
Qed.

Lemma NReducing'_sort_term_homo: forall(l:list term),
  AReduced l -> NReducing (sort_term l) = sort_term (NReducing' l).
Proof.
  intros. 
  assert (H1:=sort_ltSorted (NReducing' l)).
  assert (H2:=sort_ltSorted l). apply ltSorted_NReducing in H2.
  assert (AReduced (sort_term (NReducing' l))).
  {apply AReduced_NReducing' in H. now apply sort_AReduced in H. }
  assert (AReduced (NReducing (sort_term l))).
  {apply sort_AReduced in H. unfold NReducing. 
   apply AReduced_NReducing' in H. now apply AReduced_rev in H. }
  apply ltSorted_Permutation;auto. unfold NReducing. apply Permutation_sym.
  rewrite <- Permutation_rev.
  rewrite <- sort_ltSorted_Permutation;auto.
  - apply Permutation_preserve_NReducing'. apply sort_ltSorted_Permutation. auto.
  - apply AReduced_NReducing'. auto.
  - apply sort_AReduced. auto.

Qed. 

Lemma Reducing_lr_Ord_idpt_rev_l: forall(tl tl':list term),
  Reducing_lr_Ord (tl ++ tl') = Reducing_lr_Ord ((Reducing_lr_Ord tl) ++ tl') .
Proof. 
  intros. unfold Reducing_lr_Ord. unfold Reducing_lr at 2 3.
  rewrite <- AReducing_lr_app.
  assert(H:= AReducing_lr_Correct_Reduced (tl)).
  assert(H1:= AReducing_NReducing_AReduced_list _ H).
  assert(H2:= AReducing_UReducing_AReduced_list _ H1).
  assert(H3:= sort_AReduced _ H2). assert(H4:=AReduced_AReducing_idpt _ H3).
  rewrite H4.
  rewrite <- UReducing_sort_term_homo. 
    unfold NReducing. rewrite sort_rev. 
    rewrite <- NReducing'_sort_term_homo.
  (* rewrite <- NReducing_sort_term_homo. *)
  rewrite <- sort_term_within_l;auto. 
  rewrite NReducing'_sort_term_homo.
  remember (sort_term (Reducing_lr (tl ++ tl'))) as temp.
  rewrite <- sort_rev. subst.
  rewrite UReducing_sort_term_homo.
  assert(H5:=AReduced_AReducing_idpt _ H2). unfold NReducing in H5. rewrite <- H5.
  rewrite AReducing_lr_app. 
  assert(J:=Reducing_lr_Ord_idpt_Reducing_l tl tl'). clear H H1 H2 H3 H4 H5.
  unfold Reducing_lr_Ord in J. unfold Reducing_lr in *. unfold NReducing in J. auto.
  + apply AReduced_app. auto. apply AReducing_lr_Correct_Reduced.
  + apply AReduced_app. auto. apply AReducing_lr_Correct_Reduced.
Qed. 

Lemma Reducing_lr_Ord_idpt_rev_r: forall(tl tl':list term),
  Reducing_lr_Ord (tl ++ tl') = Reducing_lr_Ord (tl ++ (Reducing_lr_Ord tl')) .
Proof.
  intros. unfold Reducing_lr_Ord. unfold Reducing_lr at 2 3.
  rewrite <- AReducing_lr_app.
  assert(H:= AReducing_lr_Correct_Reduced (tl')).
  assert(H1:= AReducing_NReducing_AReduced_list _ H).
  assert(H2:= AReducing_UReducing_AReduced_list _ H1).
  assert(H3:= sort_AReduced _ H2). assert(H4:=AReduced_AReducing_idpt _ H3).
  rewrite H4.
  rewrite <- UReducing_sort_term_homo. unfold NReducing.
  rewrite sort_rev.
  rewrite <- NReducing'_sort_term_homo.
  rewrite <- sort_term_within_r;auto.
  rewrite NReducing'_sort_term_homo.
  remember (sort_term (Reducing_lr (tl ++ tl'))) as temp. 
  rewrite <- sort_rev. subst.
  rewrite UReducing_sort_term_homo.
  assert(H5:=AReduced_AReducing_idpt _ H2). unfold NReducing in H5. rewrite <- H5.
  rewrite AReducing_lr_app. 
  assert(J:=Reducing_lr_Ord_idpt_Reducing_r tl tl'). clear H H1 H2 H3 H4 H5.
  unfold Reducing_lr_Ord in J. unfold Reducing_lr in *. unfold NReducing in J. auto. 
  + apply AReduced_app. apply AReducing_lr_Correct_Reduced. auto.
  + apply AReduced_app. apply AReducing_lr_Correct_Reduced. auto.
Qed.
  
Lemma Reducing_lr_Ord_compat: forall(tl1 tl2 tl3 tl4:list term),
  Reducing_lr_Ord tl1 = Reducing_lr_Ord tl2 ->
  Reducing_lr_Ord tl3 = Reducing_lr_Ord tl4 ->
  Reducing_lr_Ord (tl1++tl3) = Reducing_lr_Ord (tl2++tl4).
Proof.
   intros. remember (Reducing_lr_Ord tl2) as tlr2.
   symmetry in Heqtlr2. (*
   
   *) 
   (* assert(H1:=Reducing_lr_Ord_idpt tl1 tlr2 H). *)
   assert(H1:=Reducing_lr_Ord_idpt_rev_r nil tl2). simpl in H1. rewrite Heqtlr2 in H1.
   rewrite <- H in H1 at 1.

   assert(H2:=Reducing_lr_Ord_idpt_rev_l tl1 tl3). rewrite H2.
   rewrite H1. rewrite <- Heqtlr2. rewrite <- Reducing_lr_Ord_idpt_rev_l.
   rewrite <- Reducing_lr_Ord_idpt_rev_l.

   (* assert(H3:=Reducing_lr_Ord_idpt tl3 (Reducing_lr_Ord tl4) H0). *)
   assert(H3:=Reducing_lr_Ord_idpt_rev_r nil tl4). simpl in H3. rewrite <- H0 in H3 at 1.
   rewrite Reducing_lr_Ord_idpt_rev_r. rewrite H3. rewrite <- Reducing_lr_Ord_idpt_rev_r.
   rewrite <- Reducing_lr_Ord_idpt_rev_r. auto.
Qed.

Lemma lTerm_eqv_bool_single_sound: forall (t1 t2:term),
  t1 == t2 -> lTerm_eqv_bool [t1] [t2] = true.
Proof.
  intros. induction H; apply term_beq_syn_list_correct; unfold Reducing_lr_Ord.
  - unfold Reducing_lr. simpl. rewrite <- app_nil_end. 
    rewrite <- app_nil_end. f_equal. f_equal. f_equal. now rewrite app_assoc.
  - apply Reducing_lr_Ord_term_swap.
  - unfold Reducing_lr. simpl. rewrite UNReducing_T0. 
    destruct (Oplus_term x) eqn:H;auto. rewrite <- app_nil_end.
    unfold term_to_lTerm. destruct x;auto. inversion H.
  - f_equal. unfold Reducing_lr. simpl. rewrite <- app_nil_end.
    assert(H:= NReducing_listsame (term_to_lTerm x)). rewrite H. now simpl.
  - auto.
  - apply term_beq_syn_list_correct in IHeqv. now symmetry.
  - apply term_beq_syn_list_correct in IHeqv1. 
    apply term_beq_syn_list_correct in IHeqv2.
    unfold Reducing_lr_Ord in *. congruence.
  - unfold lTerm_eqv_bool in *. apply term_beq_syn_list_correct in IHeqv1.
    apply term_beq_syn_list_correct in IHeqv2. 
    assert(H1:= Reducing_lr_Ord_compat [x] [x'] [y] [y'] IHeqv1 IHeqv2).
    simpl in *. assert(H2:= Reducing_lr_Ord_oplus x y).
    assert(H3:= Reducing_lr_Ord_oplus x' y').
    unfold Reducing_lr_Ord in *. congruence.
Qed.

Lemma lTerm_eqv_bool_single_complete: forall (t1 t2:term),
  lTerm_eqv_bool [t1] [t2] = true -> t1 == t2  .
Proof.
  intros. 
  unfold lTerm_eqv_bool in H. apply term_beq_syn_list_correct in H.
  assert(H1:=Reducing_lr_Ord_Correct_eqv [t1]).
  assert(H2:=Reducing_lr_Ord_Correct_eqv [t2]).
  rewrite H in H1. 
  assert(H3:= lr_trans [t1] (Reducing_lr_Ord [t2]) [t2] H1).
  apply lr_sym in H2. apply H3 in H2. clear H3.
  apply lTerm_eqv_ok in H2. simpl in H2.
  rewrite eqvU' in H2. now rewrite eqvU' in H2.
Qed.

(* =============================================================================== *)
(* 
This is the other direction
It says that if two terms are equivalence, then they are equal in their reduced form
*)
Lemma lTerm_eqv_bool_complete: forall (l1 l2:list term),
  l1 =l= l2 -> lTerm_eqv_bool l1 l2 = true.
Proof.
  intros. 
  unfold lTerm_eqv_bool. apply term_beq_syn_list_correct. induction H.
  - unfold Reducing_lr_Ord. f_equal.
    unfold Reducing_lr. rewrite <- AReducing_lr_app. rewrite <- AReducing_lr_app.
    simpl. remember (AReducing_lr ll) as all. remember (AReducing_lr lr) as alr.
    now rewrite UNReducing_T0_mid.
  - apply lTerm_eqv_bool_single_sound in H. unfold lTerm_eqv_bool in H.
    apply term_beq_syn_list_correct in H. unfold Reducing_lr_Ord.
    unfold Reducing_lr. simpl. assert (H1:= Reducing_lr_Ord_compat [x] [y] l2 l2 H). 
    assert(Reducing_lr_Ord l2 = Reducing_lr_Ord l2) by auto. firstorder.
    assert(Reducing_lr_Ord l1 = Reducing_lr_Ord l1) by auto.
    assert (H3:= Reducing_lr_Ord_compat l1 l1 ([x] ++ l2) ([y] ++ l2) H2 H1). now simpl in H3.
  - unfold Reducing_lr_Ord. f_equal. unfold Reducing_lr.
    simpl. rewrite <- AReducing_lr_app. unfold NReducing. rewrite NReducing'_listsame.
    now simpl.
  - induction H.
    + auto.
    + assert(Reducing_lr_Ord [x] = Reducing_lr_Ord [x]) by auto.
      assert(H1:=Reducing_lr_Ord_compat [x] [x] l l' H0 IHPermutation). now simpl in H1.
    + unfold Reducing_lr_Ord. apply Permutation_sort_same. unfold Reducing_lr.
      unfold NReducing. apply Permutation_preserve_UReducing. rewrite <- Permutation_rev.
      rewrite <- Permutation_rev.
      apply Permutation_preserve_NReducing'; try constructor. simpl.
      destruct(Oplus_term y); destruct(Oplus_term x).
      -- cut (Permutation (term_to_lTerm y ++ term_to_lTerm x)
         (term_to_lTerm x ++ term_to_lTerm y));intros. 
         assert(H1:= Permutation_app_tail (AReducing_lr l) H). repeat rewrite app_assoc. auto. 
         apply Permutation_app_comm.
      -- cut (Permutation (term_to_lTerm y ++ [x]) (x :: term_to_lTerm y));intros.
         assert(H1:= Permutation_app_tail (AReducing_lr l) H). simpl in *. 
         rewrite <- app_assoc in H1. simpl in H1. auto. apply Permutation_app_comm.
      -- cut (Permutation (y :: term_to_lTerm x) (term_to_lTerm x ++ [y]));intros.
         assert(H1:= Permutation_app_tail (AReducing_lr l) H). simpl in *. 
         rewrite <- app_assoc in H1. simpl in H1. auto. apply Permutation_sym.
         apply Permutation_app_comm.
      -- cut (Permutation (y :: [x]) (x :: [y]));intros.
         assert(H1:= Permutation_app_tail (AReducing_lr l) H). simpl in *. auto. 
         constructor.
    + congruence.
  - now assert (H2:=Reducing_lr_Ord_compat l1 l2 l3 l4 IHlTerm_eqv1 IHlTerm_eqv2).
  - congruence.
  - now symmetry.
  - auto.
  - now rewrite Reducing_lr_Ord_oplus.
Qed.


Lemma lTerm_eqv_bool_correct: forall (l1 l2:list term),
  lTerm_eqv l1 l2 <-> lTerm_eqv_bool l1 l2 = true.
Proof.
  split. apply lTerm_eqv_bool_complete.
  apply lTerm_eqv_bool_sound.
Qed.

(*
This is simpler version for the important lemma
*)
Theorem lTerm_eqv_eq_correct: forall (l1 l2:list term),
  l1 =l= l2 <-> Reducing_lr_Ord l1 = Reducing_lr_Ord l2.
Proof.
  split;intros.
  - apply lTerm_eqv_bool_correct in H. unfold lTerm_eqv_bool in H. 
    apply term_beq_syn_list_sound in H. auto.
  - apply lTerm_eqv_bool_correct. unfold lTerm_eqv_bool.
    apply term_beq_syn_list_correct. auto.
Qed.


(*
The rest are some simple lemma to rewrite a lTerm into a simpler form
comment omit
*)
Lemma term_to_lTerm_AReduced:forall(t:term),
  AReduced (term_to_lTerm t).
Proof.
  intros. induction t;simpl;try repeat constructor.
  apply AReduced_app;auto.
Qed.

Lemma AReducing_lr_term_to_lTerm:forall(t:term),
  AReducing_lr [t] = term_to_lTerm t.
Proof.
  intros. induction t;simpl;auto. now rewrite app_nil_r.
Qed.

Lemma AReducing_lr_term_to_lTerm_2:forall(t1 t2:term),
  AReducing_lr [t1;t2] = term_to_lTerm t1 ++ term_to_lTerm t2.
Proof.
  intros t1. induction t1;simpl;intros. 
  - destruct t2;simpl;auto. now rewrite app_nil_r.
  - destruct t2;simpl;auto. now rewrite app_nil_r.
  - destruct t2;simpl;auto. now rewrite app_nil_r.
Qed.

Lemma AReducing_lr_term_to_lTerm_cons:forall(t:term)(tl:lTerm),
  AReducing_lr (t::tl) = term_to_lTerm t ++ AReducing_lr tl.
Proof.
  intros. simpl. destruct t;simpl;auto.
Qed.

Lemma AReducing_lr_idpt:forall(tl:lTerm),
  AReducing_lr (tl) = AReducing_lr (AReducing_lr tl).
Proof.
  intros. assert(AReduced (AReducing_lr tl)).
  apply AReducing_lr_Correct_Reduced. apply AReduced_AReducing_idpt in H. auto.
Qed.


Lemma Term_eqv_Reduced_nil:forall(t1 t2:term),
  t1 == t2 -> Reducing_lr_Ord [t1 ; t2] = [].
Proof.
  intros. unfold Reducing_lr_Ord. unfold Reducing_lr. induction H.
  - simpl. unfold NReducing. rewrite app_nil_r. 
    assert(J:=NReducing'_listsame ((term_to_lTerm x ++ term_to_lTerm y) ++ term_to_lTerm z)).
    repeat rewrite <- app_assoc in *. rewrite J. auto.
  - simpl. assert(L:=term_to_lTerm_AReduced x). 
    assert(L1:=term_to_lTerm_AReduced y).
    remember (term_to_lTerm x) as l1. remember (term_to_lTerm y) as l2. rewrite app_nil_r.
    rewrite <- app_assoc. rewrite app_assoc. 
    rewrite <- UReducing_sort_term_homo. 
    unfold NReducing. rewrite sort_rev. assert(K:=NReducing'_sort_term_homo).
    rewrite <- K.  assert(Permutation ((l1 ++ l2) ++ l2 ++ l1) (l1 ++ l2 ++ l1 ++ l2)).
    rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_comm.
    apply Permutation_sort_same in H. rewrite H. rewrite K. rewrite app_assoc.
    rewrite NReducing'_listsame. auto. repeat apply AReduced_app;auto. repeat apply AReduced_app;auto.
  - simpl. unfold NReducing. destruct x;simpl. rewrite beq_nat_same. auto.
    unfold beq_var. rewrite <- beq_string_refl. auto.
    remember (term_to_lTerm x1) as l1. remember (term_to_lTerm x2) as l2. rewrite app_nil_r.
    rewrite NReducing'_listsame. auto.
  - simpl. assert(J:=UNReducing_T0_mid (term_to_lTerm x ++ term_to_lTerm x) nil). rewrite J.
    rewrite app_nil_r. unfold NReducing. rewrite NReducing'_listsame. auto.
  - unfold NReducing. destruct x;simpl;auto. rewrite beq_nat_same. auto.
    rewrite <- beq_string_refl. auto. rewrite app_nil_r. rewrite NReducing'_listsame. auto.
  - assert([x;y] = [x] ++ [y]). auto. assert([y;x] = [y] ++ [x]). auto.
    rewrite H0 in IHeqv. rewrite H1. rewrite <- AReducing_lr_app in *.
    clear H0 H1. rewrite <- UReducing_sort_term_homo in *.
    remember (AReducing_lr [x]) as lx. remember (AReducing_lr [y]) as ly. 
    rewrite <- IHeqv. unfold NReducing. rewrite sort_rev. rewrite sort_rev.
    repeat rewrite <- NReducing'_sort_term_homo. assert(Permutation (lx ++ ly) (ly ++ lx)).
    apply Permutation_app_comm. apply Permutation_sort_same in H0. rewrite H0. auto.
    apply AReduced_app; subst;apply AReducing_lr_Correct_Reduced.
    apply AReduced_app; subst;apply AReducing_lr_Correct_Reduced.
  - assert(Reducing_lr_Ord [] = []). auto. rewrite <- H1 in IHeqv1 at 2. rewrite <- H1 in IHeqv2 at 2.  
    assert(K:=Reducing_lr_Ord_compat _ _ _ _ IHeqv1 IHeqv2). simpl in K. rewrite H1 in K.
    clear IHeqv1 IHeqv2 H1. unfold Reducing_lr_Ord in K. unfold Reducing_lr in K. 
    repeat rewrite AReducing_lr_term_to_lTerm_cons in K. assert(AReducing_lr [] = []).
    auto. rewrite H1 in K. rewrite app_nil_r in K. rewrite AReducing_lr_term_to_lTerm_2.
    remember (term_to_lTerm x) as lx. remember (term_to_lTerm y) as ly. remember (term_to_lTerm z) as lz.
    clear H1. unfold NReducing in *. rewrite <- UReducing_sort_term_homo in K. rewrite sort_rev in K.
    rewrite <- NReducing'_sort_term_homo in K. 
    assert(Permutation (lx ++ ly ++ ly ++ lz) (ly ++ ly ++ lx ++ lz)). repeat rewrite app_assoc.
    apply Permutation_app_tail. rewrite <- app_assoc at 1. apply Permutation_app_comm.
    apply Permutation_sort_same in H1. rewrite H1 in K.  clear H1. rewrite NReducing'_sort_term_homo in K.
    rewrite <- sort_rev in K. rewrite UReducing_sort_term_homo in K. rewrite app_assoc in K.
    assert(J:=Reducing_lr_Ord_idpt_rev_l (ly++ly) (lx ++ lz)). unfold Reducing_lr_Ord in J at 1.
    unfold Reducing_lr in J. unfold NReducing in J. rewrite <- app_assoc in J.
    repeat rewrite <- AReducing_lr_app in J. 
    assert(AReduced(lx)). rewrite Heqlx. apply term_to_lTerm_AReduced. apply AReduced_AReducing_idpt in H1.
    assert(AReduced(ly)). rewrite Heqly. apply term_to_lTerm_AReduced. apply AReduced_AReducing_idpt in H2.
    assert(AReduced(lz)). rewrite Heqlz. apply term_to_lTerm_AReduced. apply AReduced_AReducing_idpt in H3.
    rewrite H1 in J. rewrite H2 in J. rewrite H3 in J. 
    unfold Reducing_lr_Ord in J at 2. unfold Reducing_lr in J. rewrite <- AReducing_lr_app in J.
    rewrite NReducing_listsame in J. simpl in J. symmetry in J. rewrite <- app_assoc in K.
    rewrite K in J. unfold Reducing_lr_Ord in J. unfold Reducing_lr in J. rewrite <- AReducing_lr_app in J.
    rewrite H1 in J. rewrite H3 in J. auto.
    repeat apply AReduced_app;subst;apply term_to_lTerm_AReduced.
    repeat apply AReduced_app;subst;apply term_to_lTerm_AReduced.
  - simpl. remember (term_to_lTerm x) as lx. remember (term_to_lTerm x') as lx'.
    remember (term_to_lTerm y) as ly. remember (term_to_lTerm y') as ly'.
    rewrite app_nil_r. rewrite <- UReducing_sort_term_homo. unfold NReducing.
    rewrite sort_rev. rewrite <- app_assoc. assert(Permutation (lx ++ ly ++ lx' ++ ly') (lx ++ lx' ++ ly ++ ly')).
    apply Permutation_app_head. rewrite app_assoc. rewrite app_assoc. apply Permutation_app_tail.
    apply Permutation_app_comm. rewrite <- NReducing'_sort_term_homo. apply Permutation_sort_same in H1.
    rewrite H1. rewrite NReducing'_sort_term_homo. rewrite <- sort_rev. rewrite UReducing_sort_term_homo.
    rewrite app_assoc. assert(K:=Reducing_lr_Ord_idpt_rev_l (lx ++ lx') (ly ++ ly')).
    unfold Reducing_lr_Ord in K at 1. unfold Reducing_lr in K.
    assert(AReduced(lx)). rewrite Heqlx. apply term_to_lTerm_AReduced. apply AReduced_AReducing_idpt in H2.
    assert(AReduced(lx')). rewrite Heqlx'. apply term_to_lTerm_AReduced. apply AReduced_AReducing_idpt in H3.
    assert(AReduced(ly)). rewrite Heqly. apply term_to_lTerm_AReduced. apply AReduced_AReducing_idpt in H4.
    assert(AReduced(ly')). rewrite Heqly'. apply term_to_lTerm_AReduced. apply AReduced_AReducing_idpt in H5.
    repeat rewrite<-AReducing_lr_app in K. rewrite H2 in K. rewrite H3 in K. rewrite H4 in K. rewrite H5 in K.
    unfold NReducing in K. rewrite K. unfold Reducing_lr_Ord. unfold Reducing_lr. 
    rewrite AReducing_lr_term_to_lTerm_2 in IHeqv1. 
    assert(AReducing_lr (lx ++ lx') = AReducing_lr lx ++ AReducing_lr lx'). symmetry.
    apply AReducing_lr_app. rewrite H6. rewrite H2. rewrite H3. rewrite Heqlx. rewrite Heqlx'. 
    rewrite IHeqv1. simpl. 
    rewrite <- AReducing_lr_app. rewrite H4. rewrite H5. rewrite AReducing_lr_term_to_lTerm_2 in IHeqv2.
    rewrite Heqly. rewrite Heqly'. auto.
    repeat apply AReduced_app;subst;apply term_to_lTerm_AReduced.
    repeat apply AReduced_app;subst;apply term_to_lTerm_AReduced.
Qed.

Lemma Reducing_lr_Ord_Permutation:forall(tl1 tl2:lTerm),
  Permutation tl1 tl2 -> Reducing_lr_Ord tl1 = Reducing_lr_Ord tl2.
Proof.
  intros. apply lr_perm in H. apply lTerm_eqv_bool_complete in H. unfold lTerm_eqv_bool in H.
  apply term_beq_syn_list_correct in H. auto.
Qed.

Lemma Reducing_lr_Ord_simpl_abbc:forall(tl1 tl2 tl3:lTerm),
  Reducing_lr_Ord (tl1 ++ tl2 ++ tl2 ++ tl3) = Reducing_lr_Ord (tl1 ++ tl3).
Proof.
  intros. unfold Reducing_lr_Ord at 1. unfold Reducing_lr. repeat rewrite <- AReducing_lr_app.
  remember (AReducing_lr tl1) as atl1.
  assert(AReduced(atl1)). rewrite Heqatl1. apply AReducing_lr_Correct_Reduced.
  remember (AReducing_lr tl2) as atl2.
  assert(AReduced(atl2)). rewrite Heqatl2. apply AReducing_lr_Correct_Reduced.
  remember (AReducing_lr tl3) as atl3.
  assert(AReduced(atl3)). rewrite Heqatl3. apply AReducing_lr_Correct_Reduced.
  apply AReduced_AReducing_idpt in H as HH.
  apply AReduced_AReducing_idpt in H1 as HH1.
  apply AReduced_AReducing_idpt in H0 as HH0.
  rewrite <- UReducing_sort_term_homo. unfold NReducing. rewrite sort_rev. 
  rewrite <- NReducing'_sort_term_homo. 
  assert(Permutation (atl1 ++ atl2 ++ atl2 ++ atl3) (atl2 ++ atl2 ++ atl1 ++ atl3)).
  repeat rewrite app_assoc. apply Permutation_app_tail. rewrite <- app_assoc. apply Permutation_app_comm.
  apply Permutation_sort_same in H2. rewrite H2. clear H2. rewrite NReducing'_sort_term_homo.
  rewrite <- sort_rev. rewrite UReducing_sort_term_homo. 
  assert(J:=Reducing_lr_Ord_idpt_rev_l (atl2 ++ atl2) (atl1 ++ atl3)). 
  unfold Reducing_lr_Ord in J at 1. unfold Reducing_lr in J. repeat rewrite <- AReducing_lr_app in J.
  rewrite HH in J. rewrite HH1 in J. rewrite HH0 in J. unfold NReducing in J. rewrite <- app_assoc in J.
  rewrite J. unfold Reducing_lr_Ord at 2. unfold Reducing_lr.
  rewrite <- AReducing_lr_app. rewrite NReducing_listsame. simpl. unfold Reducing_lr_Ord.
  unfold Reducing_lr. repeat rewrite <- AReducing_lr_app. congruence. 
  subst. repeat apply AReduced_app;auto. subst. repeat apply AReduced_app;auto.
Qed.

Lemma Reducing_lr_Ord_simpl_aba:forall(tl1 tl2:lTerm),
  Reducing_lr_Ord (tl1 ++ tl2 ++ tl1) = Reducing_lr_Ord (tl2).
Proof.
  intros. unfold Reducing_lr_Ord at 1. unfold Reducing_lr. repeat rewrite <- AReducing_lr_app.
  remember (AReducing_lr tl1) as atl1.
  assert(AReduced(atl1)). rewrite Heqatl1. apply AReducing_lr_Correct_Reduced.
  remember (AReducing_lr tl2) as atl2.
  assert(AReduced(atl2)). rewrite Heqatl2. apply AReducing_lr_Correct_Reduced.
  apply AReduced_AReducing_idpt in H as HH.
  apply AReduced_AReducing_idpt in H0 as HH0.
  rewrite <- UReducing_sort_term_homo. unfold NReducing. rewrite sort_rev. 
  rewrite <- NReducing'_sort_term_homo. 
  assert(Permutation (atl1 ++ atl2 ++ atl1) (atl1 ++ atl1 ++ atl2)).
  apply Permutation_app_head. apply Permutation_app_comm.
  apply Permutation_sort_same in H1. rewrite H1. clear H1. rewrite NReducing'_sort_term_homo.
  rewrite <- sort_rev. rewrite UReducing_sort_term_homo. 
  assert(J:=Reducing_lr_Ord_idpt_rev_l (atl1 ++ atl1) atl2). 
  unfold Reducing_lr_Ord in J at 1. unfold Reducing_lr in J. repeat rewrite <- AReducing_lr_app in J.
  rewrite HH in J. rewrite HH0 in J. unfold NReducing in J. rewrite <- app_assoc in J.
  rewrite J. unfold Reducing_lr_Ord at 2. unfold Reducing_lr.
  rewrite <- AReducing_lr_app. rewrite NReducing_listsame. simpl. unfold Reducing_lr_Ord.
  unfold Reducing_lr. repeat rewrite <- AReducing_lr_app. congruence. 
  subst. repeat apply AReduced_app;auto. subst. repeat apply AReduced_app;auto.
Qed.


Lemma Reducing_lr_Ord_simpl_abac:forall(tl1 tl2 tl3:lTerm),
  Reducing_lr_Ord (tl1 ++ tl2 ++ tl1 ++ tl3) = Reducing_lr_Ord (tl2 ++ tl3).
Proof.
  intros. unfold Reducing_lr_Ord at 1. unfold Reducing_lr. repeat rewrite <- AReducing_lr_app.
  remember (AReducing_lr tl1) as atl1.
  assert(AReduced(atl1)). rewrite Heqatl1. apply AReducing_lr_Correct_Reduced.
  remember (AReducing_lr tl2) as atl2.
  assert(AReduced(atl2)). rewrite Heqatl2. apply AReducing_lr_Correct_Reduced.
  remember (AReducing_lr tl3) as atl3.
  assert(AReduced(atl3)). rewrite Heqatl3. apply AReducing_lr_Correct_Reduced.
  apply AReduced_AReducing_idpt in H as HH.
  apply AReduced_AReducing_idpt in H0 as HH0.
  apply AReduced_AReducing_idpt in H1 as HH1.
  rewrite <- UReducing_sort_term_homo. unfold NReducing. rewrite sort_rev. 
  rewrite <- NReducing'_sort_term_homo. 
  assert(Permutation (atl1 ++ atl2 ++ atl1 ++ atl3) (atl1 ++ atl1 ++ atl2 ++ atl3)).
  apply Permutation_app_head. repeat rewrite app_assoc. apply Permutation_app_tail.
  apply Permutation_app_comm.
  apply Permutation_sort_same in H2. rewrite H2. clear H2. rewrite NReducing'_sort_term_homo.
  rewrite <- sort_rev. rewrite UReducing_sort_term_homo. 
  assert(J:=Reducing_lr_Ord_idpt_rev_l (atl1 ++ atl1) (atl2 ++ atl3)). 
  unfold Reducing_lr_Ord in J at 1. unfold Reducing_lr in J. repeat rewrite <- AReducing_lr_app in J.
  rewrite HH in J. rewrite HH0 in J. rewrite HH1 in J.
   unfold NReducing in J. rewrite <- app_assoc in J.
  rewrite J. unfold Reducing_lr_Ord at 2. unfold Reducing_lr.
  rewrite <- AReducing_lr_app. rewrite NReducing_listsame. simpl. unfold Reducing_lr_Ord.
  unfold Reducing_lr. repeat rewrite <- AReducing_lr_app. congruence. 
  subst. repeat apply AReduced_app;auto. subst. repeat apply AReduced_app;auto.
Qed.
  

Lemma lTerm_eqv_Reduced_nil:forall(tl1 tl2:lTerm),
  tl1 =l= tl2 -> Reducing_lr_Ord (tl1 ++ tl2) = [].
Proof.
  intros. induction H.
  - unfold Reducing_lr_Ord. unfold Reducing_lr. repeat rewrite <- AReducing_lr_app.
    simpl. rewrite app_assoc. rewrite UNReducing_T0_mid. rewrite <- app_assoc.
    rewrite NReducing_listsame. auto.
  - apply Term_eqv_Reduced_nil in H. 
    assert(Permutation ((l1 ++ x :: l2) ++ l1 ++ y :: l2)
    ([x] ++ [y] ++ (l1 ++ l2) ++ l1 ++ l2)). assert(y :: l2 = [y]++l2). 
    auto. rewrite H0. repeat rewrite app_assoc. apply Permutation_app_tail.
    repeat rewrite <- app_assoc. assert([x] ++ [y] ++ l1 ++ l2 ++ l1 = ([x] ++ [y] ++ l1 ++ l2) ++ l1).
    repeat rewrite app_assoc. auto. rewrite H1. 
    cut (Permutation ((x :: l2) ++ l1 ++ [y]) ([x] ++ [y] ++ l1 ++ l2)). intro.
    rewrite H2. apply Permutation_app_comm. simpl. constructor. 
    assert(y :: l1 ++ l2 = (y :: l1) ++ l2). auto. rewrite H2. 
    cut (Permutation (l1 ++ [y]) (y :: l1)). intro. rewrite H3. apply Permutation_app_comm.
    assert(y::l1 = [y] ++ l1). auto. rewrite H3. apply Permutation_app_comm.
    apply Reducing_lr_Ord_Permutation in H0. rewrite H0. 
    assert(J:=Reducing_lr_Ord_idpt_rev_l ([x] ++ [y]) ((l1 ++ l2) ++ l1 ++ l2)).
    rewrite app_assoc. rewrite J. simpl Reducing_lr_Ord at 2. rewrite H. simpl. 
    unfold Reducing_lr_Ord. unfold Reducing_lr. repeat rewrite <- AReducing_lr_app.
    rewrite NReducing_listsame. auto.
  - unfold Reducing_lr_Ord. unfold Reducing_lr. repeat rewrite <- AReducing_lr_app.
    simpl. assert(J:=UNReducing_T0_mid (AReducing_lr l ++ AReducing_lr l) nil). rewrite J.
    rewrite app_nil_r. rewrite NReducing_listsame. auto.
  - unfold Reducing_lr_Ord. unfold Reducing_lr. 
    rewrite <- AReducing_lr_app. induction H.
    + auto.
    + repeat rewrite AReducing_lr_term_to_lTerm_cons. remember (term_to_lTerm x) as lx.
      rewrite <- app_assoc. assert(J:=Reducing_lr_Ord_simpl_abac lx (AReducing_lr l) (AReducing_lr l')).
      unfold Reducing_lr_Ord in J. unfold Reducing_lr in J.
      repeat rewrite <- AReducing_lr_app in J. repeat rewrite <- AReducing_lr_idpt in *. 
      assert(AReduced (lx)). subst. apply term_to_lTerm_AReduced. apply AReduced_AReducing_idpt in H0.
      rewrite H0 in *. rewrite J. auto.
    + repeat rewrite AReducing_lr_term_to_lTerm_cons. repeat rewrite <- app_assoc.
      assert(AReduced (term_to_lTerm x)). apply term_to_lTerm_AReduced.
      assert(AReduced (term_to_lTerm y)). apply term_to_lTerm_AReduced.
      remember (term_to_lTerm x) as lx. remember (term_to_lTerm y) as ly.
      assert(J:=Reducing_lr_Ord_simpl_abac ly (lx ++ AReducing_lr l ++ lx) (AReducing_lr l)).
      repeat rewrite <- app_assoc in J. unfold Reducing_lr_Ord in J. unfold Reducing_lr in J.
      repeat rewrite <- AReducing_lr_app in J. repeat rewrite <- AReducing_lr_idpt in *.
      apply AReduced_AReducing_idpt in H as K. apply AReduced_AReducing_idpt in H0 as K0.
      rewrite K in J. rewrite K0 in J. rewrite J. clear J.
      assert(J:=Reducing_lr_Ord_simpl_abac lx (AReducing_lr l) (AReducing_lr l)).
      repeat rewrite <- app_assoc in J. unfold Reducing_lr_Ord in J. unfold Reducing_lr in J.
      repeat rewrite <- AReducing_lr_app in J. repeat rewrite <- AReducing_lr_idpt in *.
      rewrite K in J. rewrite J. rewrite NReducing_listsame. auto.
    + assert(Reducing_lr_Ord [] = []). auto. rewrite <- H1 in IHPermutation1.
      rewrite <- H1 in IHPermutation2. rewrite AReducing_lr_app in IHPermutation1.
      rewrite AReducing_lr_app in IHPermutation2.
      assert(K:=Reducing_lr_Ord_compat _ _ _ _ IHPermutation1 IHPermutation2).
      simpl in K. rewrite H1 in K. rewrite <- app_assoc in K.
      rewrite Reducing_lr_Ord_simpl_abbc in K. unfold Reducing_lr_Ord in K.
      unfold Reducing_lr in K. now rewrite <- AReducing_lr_app in K.
  - assert(Reducing_lr_Ord [] = []). auto. rewrite <- H1 in IHlTerm_eqv1.
    rewrite <- H1 in IHlTerm_eqv2.  
    assert(K:=Reducing_lr_Ord_compat _ _ _ _ IHlTerm_eqv1 IHlTerm_eqv2). simpl in K.
    rewrite H1 in K. assert(Permutation ((l1 ++ l2) ++ l3 ++ l4) ((l1 ++ l3) ++ l2 ++ l4)).
    repeat rewrite app_assoc. apply Permutation_app_tail. repeat rewrite <- app_assoc. 
    apply Permutation_app_head. apply Permutation_app_comm.
    apply Reducing_lr_Ord_Permutation in H2. rewrite H2 in K. auto.
  - assert(Reducing_lr_Ord [] = []). auto. rewrite <- H1 in IHlTerm_eqv1.
    rewrite <- H1 in IHlTerm_eqv2.  
    assert(K:=Reducing_lr_Ord_compat _ _ _ _ IHlTerm_eqv1 IHlTerm_eqv2). simpl in K.
    rewrite H1 in K. rewrite <- app_assoc in K. rewrite Reducing_lr_Ord_simpl_abbc in K.
    auto.
  - assert(Permutation (l1 ++ l2) (l2 ++ l1)). apply Permutation_app_comm. apply Reducing_lr_Ord_Permutation in H0.
    congruence.
  - assert (H:=Reducing_lr_Ord_simpl_aba l1 nil). simpl in H. rewrite H. auto.
  - unfold Reducing_lr_Ord. unfold Reducing_lr. repeat rewrite <- AReducing_lr_app.
    simpl AReducing_lr at 1. rewrite AReducing_lr_term_to_lTerm_2. rewrite app_nil_r.
    rewrite NReducing_listsame. auto.
Qed.

Lemma lTerm_eqv_lTerm_eqv_nil:forall(tl1 tl2:lTerm),
  tl1 =l= tl2 -> tl1 ++ tl2 =l= [].
Proof.
  intros. apply lTerm_eqv_bool_correct. unfold lTerm_eqv_bool.
  apply term_beq_syn_list_correct. apply lTerm_eqv_Reduced_nil. auto.
Qed. 
