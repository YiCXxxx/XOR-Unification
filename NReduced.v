(* 

This file Defines the Second rewriting rules, NReducing, 
i.e. remove every same even number of term in a lTerm, and keep only one for every same odd number term
and we called the reduced form from NReducing - NReduced,
if a lTerm is NReduced, then every term in the lTerm has no exact same term in the lTerm because other wise it got n_add.

Example: 
- [], [V v], [C 1;C 2] is NReduced
- [C1 +' C1], [C 1 ;C 2; C 3 +' C1] is not NReduced

Then defines the:
- Prop for NReduced
- function for NReducing

And proves the important theorem:

Theorem NReducing_Correct_alllist: forall (tl : lTerm),
    AReduced tl -> NReduced (NReducing tl).
  - This Theorem says that after NReducing, every term is NReduced

Theorem NReducing_eqv: forall (tl:lTerm),
  (NReducing tl) =l= tl.
  - This Theorem says that after NReducing, it is lTerm_eqv to the original lTerm

Lemma NReduced_NReducing: forall (tl :lTerm),
  NReduced (tl) -> NReducing tl = tl.
  - This Theorem says that NReducing is an idempotent function. 
    This one is not so important at this moment, but it is very crucial for later proof.

Note:
  * Some Theorem takes in an extra assumptions that the lTerm has to be AReduced first.
    This will not affect the rewrite system because in the whole rewrite system we will just do AReducing first.

  * NReducing is the rev of NReducing' is because the functions applys n_add recursively, to achieve NReducing being
    idempotent, reverse the list back is neccessary.
    If not fliping it back will not change the first two Theorem.
*)

From XORUnif Require Export AReduced.

(*
This is a general illustraition of why we need NReducing.
We want to change every lTerm from lhs to rhs
*)
Lemma NReducing_Base:forall(lt1 lt2 lt3:lTerm)(t:term),
  lt1 ++ [t] ++ lt2 ++ [t] ++ lt3 =l= lt1 ++ lt2 ++ lt3.
Proof.
  intros. assert(Permutation (lt1 ++ [t] ++ lt2 ++ [t] ++ lt3) ([t] ++ [t] ++ lt1 ++  lt2 ++ lt3)).
  {repeat rewrite app_assoc. apply Permutation_app_tail. repeat rewrite <- app_assoc. 
   rewrite <- Permutation_cons_append. assert (lt1 ++ [t] ++ t :: lt2 = lt1 ++ [t] ++ [t] ++ lt2).
   auto. rewrite H. repeat rewrite app_assoc. apply Permutation_app_tail. repeat rewrite <- app_assoc.
   symmetry. rewrite app_assoc. apply Permutation_app_comm. }
  apply lr_perm in H. assert(H1:=lr_trans _ _ (lt1 ++ lt2 ++ lt3) H). apply H1.
  clear H1 H. assert(H1:=lr_compat ([t]++[t]) nil (lt1++lt2++lt3)(lt1++lt2++lt3)).
  simpl in *. apply H1. assert(H2:=lr_N [t]). simpl in H2.
  clear H1 H2. apply lTerm_eqv_ok. simpl. rewrite eqvU'. apply eqvN. apply lr_relf.
Qed.

Inductive NReduced:lTerm->Prop:=
|NReduced_nil : NReduced []
|NReduced_cons_const :  forall (n : nat) (tl : lTerm),
      ~ In (C n) tl -> NReduced tl -> NReduced ((C n) :: tl)
|NReduced_cons_var :  forall (v : var) (tl : lTerm),
      ~ In (V v) tl -> NReduced tl -> NReduced ((V v) :: tl).

(*
if a lTerm is NReduced, then remove the first term in the lTerm still result in a NReduced lTerm
*)
Lemma NReduced_remove1: forall (t:term) (tl:lTerm),
  NReduced (t::tl)-> NReduced (tl).
Proof.
  intros. inversion H; easy.
Qed.

(*
if a lTerm is NReduced, then remove any term in/not in the lTerm still result in a NReduced lTerm
*)
Lemma remove_NReduced: forall (t:term) (tl:lTerm),
  NReduced (tl) -> NReduced (remove t tl).
Proof.
  intros. destruct (In_dec t tl).
  - induction tl.
    + inversion i.
    + inversion i. rewrite H0. simpl. rewrite term_beq_syn_relf.
      now inversion H. 
      simpl. destruct (term_beq_syn a t) eqn: H1.
      -- now apply NReduced_remove1 in H.
      -- apply NReduced_remove1 in H as H2. 
         apply IHtl in H0; try easy. inversion H;subst;
         constructor; try easy; now apply not_In_remove.
  - apply remove_noop in n. now rewrite n.
Qed.

(*
if a lTerm is NReduced, then this lTerm has no duplicates
*)
Lemma NReduced_NoDup: forall (tl:lTerm),
  NReduced tl -> NoDup tl.
Proof.
  intros. induction tl.
  - constructor.
  - inversion H; subst.
    + constructor. easy. firstorder.
    + constructor. easy. firstorder.
Qed.

(*
if a lTerm is AReduced and Nodup, then this lTerm is NReduced
*)
Lemma NoDup_NReduced: forall (tl:lTerm),
  AReduced tl-> NoDup tl -> NReduced tl.
Proof.
  intros. induction H.
  - constructor.
  - inversion H0;subst. constructor. easy. firstorder. 
  - inversion H0; subst; constructor. easy. firstorder.
Qed.
  

(*
Note that this is a recursive function, so after NReducing' the order of the list is reversed
*)
Fixpoint NReducing'(tl:lTerm):lTerm:=
  match tl with
  |[] => []
  |t::tl => (n_add t (NReducing' tl))
  end.

(*
So we reverse it back and can achieve idempotency
*)
Definition NReducing (tl:lTerm):lTerm:=
  rev(NReducing' tl).

(*
if a lTerm has no duplicates, then remove any term in/not in the lTerm will result in a lTerm with no dup
*)
Lemma remove_NoDup:forall(t:term)(tl:lTerm),
  NoDup tl -> NoDup (remove t tl).
Proof.
  intros. induction H;simpl.
  - constructor.
  - destruct (term_beq_syn x t). auto.
    constructor. now apply not_In_remove. auto.
Qed.

(*
simpl lemma for n_add
*)
Lemma not_in_n_add:forall(t1 t2:term)(tl:lTerm),
  t1 <> t2 -> ~ In t1 tl -> ~ In t1 (n_add t2 tl).
Proof.
  intros. induction tl.
  - simpl. intro. destruct H1. symmetry in H1; firstorder. inversion H1.
  - apply not_in_cons in H0. destruct H0. firstorder. simpl.
    destruct (term_beq_syn a t2) eqn:H3. auto. intro. inversion H4.
    symmetry in H5; firstorder. firstorder.
Qed.

(*
if a lTerm has no duplicates, then n_add in any term result in a lTerm with no duplicates.
*)
Lemma n_add_NoDup:forall(t:term)(tl:lTerm),
  NoDup tl -> NoDup (n_add t tl).
Proof.
  intros. induction H;simpl.
  - constructor. intro H; inversion H. constructor.
  - destruct (term_beq_syn x t) eqn:H1. auto. constructor.
    apply term_beq_syn_false_iff in H1. 
    apply (not_in_n_add x t l) in H1; auto. auto.
Qed.


(*
NReduced no order
*)
Lemma NReduced_NoOrder: forall (t:term)(tl : lTerm),
    NReduced (t::tl) -> NReduced (tl++[t]).
Proof.
    intros. induction tl. now simpl. inversion H;subst. 
    - inversion H3; subst.
      + assert(NReduced (C n :: tl)). constructor. 
        apply not_in_cons in H2. now destruct H2. easy. apply IHtl in H0.
        simpl. constructor. apply ListUtil.notin_app. split.
        easy. intro. apply not_in_cons in H2. destruct H2. inversion H1. now apply H2 in H7.
        inversion H7. easy.
      + assert(NReduced (C n :: tl)). constructor. 
        apply not_in_cons in H2. now destruct H2. easy. apply IHtl in H0.
        simpl. constructor. apply ListUtil.notin_app. split.
        easy. intro. apply not_in_cons in H2. destruct H2. inversion H1. now apply H2 in H7.
        inversion H7. easy.
    - inversion H3; subst.
      + assert(NReduced (V v :: tl)). constructor. 
        apply not_in_cons in H2. now destruct H2. inversion H3;subst. easy. simpl.
        constructor. apply ListUtil.notin_app. split.
        easy. intro. apply not_in_cons in H2. destruct H2. inversion H1. now apply H2 in H7.
        inversion H7. now apply IHtl in H0.
      + assert(NReduced (V v :: tl)). constructor. 
        apply not_in_cons in H2. now destruct H2. inversion H3;subst. easy. simpl.
        constructor. apply ListUtil.notin_app. split.
        easy. intro. apply not_in_cons in H2. destruct H2. inversion H1. now apply H2 in H7.
        inversion H7. now apply IHtl in H0.
Qed.


(*
NReduced no order
*)
Lemma rev_NReduced: forall (tl:lTerm),
  NReduced (tl) -> NReduced (rev tl).
Proof.
  intros. induction tl;simpl.
  - constructor.
  - apply NReduced_NoOrder. inversion H;subst.
    + constructor. intro. apply in_rev in H0. now apply H2 in H0. firstorder.
    + constructor. intro. apply in_rev in H0. now apply H2 in H0. firstorder.
Qed.


Lemma list_length: forall(l1 l2:lTerm),
  l1 = l2 -> Datatypes.length l1 = Datatypes.length l2.
Proof.
  intros. now rewrite H.
Qed.

(*
NReduced no order
*)
Lemma rev_NReduced_back: forall (tl:lTerm),
  NReduced (rev tl) -> NReduced (tl).
Proof.
  intros. inversion H;simpl.
  - assert (H2:= rev_length tl).
    apply list_length in H1. rewrite H2 in H1. simpl in H1.
    symmetry in H1. apply ListUtil.length_0 in H1.
    rewrite H1. constructor.
  - apply NReduced_NoDup in H as H3. apply NoDup_rev in H3. 
    rewrite rev_involutive in H3.
    assert(rev(C n :: tl0) = rev tl0 ++ [C n] ).
    + induction tl0;simpl. easy. easy.
    + assert (rev (C n :: tl0) = rev (rev tl)). now rewrite H0. rewrite rev_involutive in H5.
       rewrite <- H5. simpl. apply NReduced_NoOrder. constructor. intro. apply 
       ListUtil.in_rev in H6. rewrite rev_involutive in H6. now apply H1 in H6.
       now apply rev_NReduced in H2.
  - apply NReduced_NoDup in H as H3. apply NoDup_rev in H3. 
    rewrite rev_involutive in H3.
    assert(rev(V v :: tl0) = rev tl0 ++ [V v] ).
    + induction tl0;simpl. easy. easy.
    + assert (rev (V v :: tl0) = rev (rev tl)). now rewrite H0. rewrite rev_involutive in H5.
      rewrite <- H5. simpl. apply NReduced_NoOrder. constructor. intro. apply 
      ListUtil.in_rev in H6. rewrite rev_involutive in H6. now apply H1 in H6.
      now apply rev_NReduced in H2.
Qed.

(*
if any arbitrary lTerm tl is AReduced. then after NReducing' it is NReduced
*)
Lemma NReducing'_Correct_Reduced_list: forall (tl : lTerm),
    AReduced tl-> NReduced (NReducing' tl).
Proof.
  intros. induction tl;simpl.
  - constructor.
  - simpl. destruct(In_dec a (NReducing' tl)).
    + apply n_add_In in i. rewrite i. inversion H;subst;firstorder; now apply remove_NReduced.
    + apply n_add_not_In in n as H1. rewrite H1. apply NReduced_NoOrder.
      inversion H;subst;firstorder; now constructor.
Qed.

(*
if any arbitrary lTerm tl is AReduced. then after NReducing it is NReduced
*)
Theorem NReducing_Correct_alllist: forall (tl : lTerm),
    AReduced tl -> NReduced (NReducing tl).
Proof.
    intros. induction tl;simpl. constructor.
    unfold NReducing in *. apply rev_NReduced.
    assert(b:= In_dec a (NReducing' tl)). destruct b.
    - simpl.
      apply n_add_In in i. rewrite i. inversion H;subst;firstorder;
      apply remove_NReduced; now apply rev_NReduced_back. 
    - inversion H; subst; firstorder;
      now apply NReducing'_Correct_Reduced_list.
Qed.

(* Not Used *)
Lemma NReducing_Correct_Reduced: forall (t : term),
    NReduced (NReducing (term_to_lTerm t)).
Proof.
    intros. induction t; simpl.
    - constructor. now simpl. constructor.
    - constructor. now simpl. constructor.
    - assert(b1:= AReducing_Correct_Reduced t1);
      assert(b2:= AReducing_Correct_Reduced t2).
      unfold AReducing in b1, b2.
      assert(c:=AReduced_app (term_to_lTerm t1)(term_to_lTerm t2) b1 b2).
      now assert(d:= NReducing_Correct_alllist (term_to_lTerm t1 ++ term_to_lTerm t2)c).
Qed.

Lemma NReduced_remove: forall (tl:lTerm)(t:term),
  NReduced (tl) -> NReduced (remove t tl).
Proof.
  intros. induction H.
  - simpl. constructor.
  - simpl. destruct t. destruct(NatUtil.beq_nat n n0). easy. 
    constructor. assert(a:=not_In_remove (C n) (C n0)). now apply a.
    easy. constructor. now apply (not_In_remove (C n) (V v)). easy.
    constructor. now apply (not_In_remove (C n) (t1 +' t2)). easy.
  - simpl. destruct t. constructor. assert(a:=not_In_remove (V v) (C n)). now apply a.
    easy. destruct (beq_var v v0). easy. constructor. 
    now apply (not_In_remove (V v) (V v0)). easy.
    constructor. now apply (not_In_remove (V v) (t1 +' t2)). easy.
Qed.


Theorem NReducing_eqv: forall (tl:lTerm),
  (NReducing tl) =l= tl.
Proof.
  intros. induction tl.
  - simpl. constructor;constructor.
  - simpl. unfold NReducing in *. 
    assert(H1:=list_eqv_rev (NReducing' tl)).
    assert(H2:=list_eqv_rev (NReducing' (a::tl))).
    assert(H3:=lr_trans (NReducing' tl) (rev (NReducing' tl)) tl H1 IHtl).
    assert(H4:=lr_trans (rev (NReducing' (a :: tl))) (NReducing' (a :: tl))  (a::tl)).
    apply H4. now apply lr_sym in H2. clear H2. clear H4. clear H1.
    destruct (In_dec a (NReducing' tl));simpl.
    + apply n_add_In in i as H.
      assert(b:=n_add_cons_eqv (NReducing' tl) a). 
      apply lr_trans with (a :: NReducing' tl). easy. 
      now apply lTerm_eqv_cons_compat.
    + apply n_add_not_In in n. rewrite n. 
      assert(b:=lr_compat (NReducing' tl) tl [a] [a]).
      assert(lTerm_eqv (a::tl)(tl++[a])).
      assert (a :: tl = [a]++tl)%list. now simpl. rewrite H. constructor.
      apply Permutation_app_comm. apply lr_trans with (tl ++ [a])%list.
      apply b;auto. apply lr_relf. now apply lr_sym. 
Qed.

(*Not Used*)
Lemma NReducing_Correct_eqv: forall (t : term),
  t == lTerm_to_term (NReducing (term_to_lTerm t)).
Proof.
  intros. assert(H:=AReduced_Correct_eqv t). rewrite H at 1.
  unfold AReducing. apply lTerm_eqv_ok. 
  assert(a:=NReducing_eqv (term_to_lTerm t)). now apply lr_sym.
Qed.

(*
remove any term will of a lTerm is included in the same lTerm
*)
Lemma remove_incl:forall (t:term)(tl:list term),
  incl (remove t tl) tl.
Proof.
  intros. induction tl; simpl. easy.
  destruct (term_beq_syn a t) eqn:H.
  - apply incl_tl. apply incl_refl.
  - apply incl_cons. now left. now apply incl_tl.
Qed.

(*
if a term is not in an lTerm, then this term is not in the lTerm after NReducing'
*)
Lemma not_In_Reduced:forall (t:term)(tl:lTerm),
  ~ In t tl -> ~ In t (NReducing' tl).
Proof.
  intros. intro. apply H. clear H. induction tl.
  - now simpl in H0.
  - simpl in H0.
    destruct (In_dec a (NReducing' tl)). 
    + apply n_add_In in i. rewrite i in H0. apply remove_incl in H0. 
      apply IHtl in H0. now right.
    + apply n_add_not_In in n. rewrite n in H0. 
      apply in_app_or in H0. destruct H0.
      -- firstorder.
      -- inversion H. now left. inversion H0.
Qed.
    
(*
Important Theorem about idempotency
*)
Theorem NReduced_NReducing: forall (tl :lTerm),
  NReduced (tl) -> NReducing tl = tl.
Proof.
  intros. induction tl.
  - now simpl.
  - inversion H;subst.
    + unfold NReducing. simpl. apply not_In_Reduced in H2. apply n_add_not_In in H2.
      rewrite H2. apply IHtl in H3. unfold NReducing in H3. rewrite rev_simp.
      now rewrite H3.
    + unfold NReducing. simpl. apply not_In_Reduced in H2. apply n_add_not_In in H2.
      rewrite H2. apply IHtl in H3. unfold NReducing in H3. rewrite rev_simp.
      now rewrite H3.
Qed.

(*
a simple rewrite rule for NReducing
*)
Lemma NReducing_term_same:forall(t:term),
  NReducing ([t;t]) = [].
Proof.
  intros. unfold NReducing. simpl. rewrite term_beq_syn_relf. now simpl.
Qed.

(*
count_occ no order
*)
Lemma count_occ_order_does_not_matter: forall(l1 l2:lTerm)(t:term),
  count_occ term_beq_syn_dec (l1++l2) t = count_occ term_beq_syn_dec (l2++l1) t.
Proof.
  intros. rewrite count_occ_app.
  rewrite count_occ_app. lia.
Qed.

(*
count_occ remove one term the total number decrease one
*)
Lemma count_remove : forall n t l, 
  count_occ term_beq_syn_dec l t = S n
  ->
  count_occ term_beq_syn_dec (remove t l) t = n.
Proof.
  intros. induction l. inversion H.
  simpl in *. destruct(term_beq_syn_dec a t).
  - rewrite e in *. rewrite term_beq_syn_relf. injection H; now intros.
  - apply term_beq_syn_false_iff in n0. rewrite n0.
    simpl in *. destruct(term_beq_syn_dec a t).
    apply term_beq_syn_false_iff in n0. now apply n0 in e.
    firstorder.
Qed.


(*
n_add a different term the count does not change
*)
Lemma n_add_neq_count: forall t1 t2 l,
  t1 <> t2 -> 
    count_occ term_beq_syn_dec (n_add t1 l) t2 = count_occ term_beq_syn_dec l t2.
Proof.
  intros. destruct (In_dec t1 l). 
  induction l;simpl in *. inversion i.
  destruct i.
  -- rewrite H0. rewrite term_beq_syn_relf. 
     destruct (term_beq_syn_dec t1 t2).
     ++ now apply H in e.
     ++ auto.
  -- apply IHl in H0. destruct(term_beq_syn a t1) eqn:H2.
    ++ destruct(term_beq_syn_dec a t2). apply term_beq_syn_true_iff in H2.
       rewrite <- H2 in H. rewrite e in H. now exfalso. auto.
    ++ destruct(term_beq_syn_dec a t2). rewrite e. simpl. 
       destruct (term_beq_syn_dec t2 t2). now f_equal. now exfalso.
       simpl. destruct (term_beq_syn_dec a t2). now apply n in e.
       auto.
  -- apply n_add_not_In in n. rewrite n. rewrite count_occ_app.
     simpl. destruct (term_beq_syn_dec t1 t2). firstorder. lia.
Qed.

(*
count_occ plus one or minus one after n_add
*)
Lemma count_n_add : forall l x y,
    count_occ term_beq_syn_dec (n_add y l) x =
    if term_beq_syn_dec y x
    then match count_occ term_beq_syn_dec l x with
         | 0 => 1
         | S p => p
         end
    else  count_occ term_beq_syn_dec l x.
Proof.
  intros. destruct (term_beq_syn_dec y x).
  - destruct(count_occ term_beq_syn_dec l x) eqn:H1.
    + rewrite e in *. apply count_occ_not_In in H1 as H2.
      apply n_add_not_In in H2. rewrite H2. rewrite count_occ_app.
      simpl. destruct (term_beq_syn_dec x x). rewrite H1. auto.
      unfold not in n. now exfalso.
    + rewrite e in *. assert(count_occ term_beq_syn_dec l x>0).
      rewrite H1. lia. apply count_occ_In in H.
      apply n_add_In in H. rewrite H. apply count_remove. auto.
  - now apply n_add_neq_count.
Qed.

(*
a natural number can only be even or odd
*)
Lemma Even_Odd_dec n : {Nat.Even n} + {Nat.Odd n}.
Proof.
  induction n. left. now exists 0.
  induction IHn.
  - right. destruct a. exists x. lia.
  - left. destruct b. exists (x+1). lia.
Qed.

(*
after NReducing' the count_occ is either 0 or 1
*)
Lemma count_NReducing'_1_0 l:
  forall x, count_occ term_beq_syn_dec (NReducing' l) x =
           if Even_Odd_dec (count_occ term_beq_syn_dec l x)
           then 0
           else 1.
Proof.
  intros. induction l;simpl. 
  - destruct (Even_Odd_dec 0). auto. inversion o. lia.
  - destruct (term_beq_syn_dec a x).
    + rewrite e; simpl. rewrite count_n_add.
      destruct (term_beq_syn_dec x x). 
      -- rewrite IHl. destruct (Even_Odd_dec (count_occ term_beq_syn_dec l x)).
         apply Nat.Odd_succ in e1 as e2. destruct(Even_Odd_dec (S (count_occ term_beq_syn_dec l x))).
         inversion e3. inversion e2. rewrite H0 in H. lia. auto.
         
         destruct(Even_Odd_dec (S (count_occ term_beq_syn_dec l x))).
         auto. apply Nat.Even_succ in o as e2.
         inversion e2. inversion o0. rewrite H0 in H. lia. 
      -- contradiction.
    + rewrite n_add_neq_count. auto. auto.          
  Qed.

(*
every term in the product of two same lTerm appended has even number of count_occ
*)
Lemma same_list_even_el:forall(l:list term)(t:term),
  Nat.Even (count_occ term_beq_syn_dec (l++l) t).
Proof.
  intros. induction l. simpl. now exists 0.
  simpl. destruct(term_beq_syn_dec a t).
  - rewrite e. simpl. destruct IHl. 
    assert(H1:=count_occ_order_does_not_matter l (t::l) t). rewrite H1. simpl.
    destruct (term_beq_syn_dec t t). rewrite H. exists (x+1). lia. 
    unfold not in n. exfalso. apply n. auto.
  - assert(H1:=count_occ_order_does_not_matter l (a::l) t). rewrite H1. simpl.
    destruct (term_beq_syn_dec a t). unfold not in n. exfalso. now apply n in e.
    auto.
Qed.


(*
if a term has even count_occ in an lTerm, then it is not in the NReducing' of the lTerm
*)
Lemma NReducing'_notIn t l:
  Nat.Even (count_occ term_beq_syn_dec l t)
  -> ~ In t (NReducing' l).
Proof. 
  intros. 
  assert(H0:= count_NReducing'_1_0 l t). 
  destruct (Even_Odd_dec (count_occ term_beq_syn_dec l t)).
  - now apply count_occ_not_In in H0.
  - destruct H. destruct o. rewrite H1 in H. lia.
Qed.

(*
if a term has odd count_occ in an lTerm, then it is in the NReducing' of the lTerm
*)
Lemma NReducing'_In t l:
  Nat.Odd (count_occ term_beq_syn_dec l t)
  -> In t (NReducing' l).
Proof.
  intros. assert(H0:= count_NReducing'_1_0 l t). 
  destruct (Even_Odd_dec (count_occ term_beq_syn_dec l t)).
  - inversion H. inversion e. lia. 
  - assert(H1:=count_occ_In term_beq_syn_dec (NReducing' l) t). apply H1. lia.
Qed.
  

(*
if for all different term, it is not in a lTerm, then the lTerm is empty.
*)
Lemma forall_Not_In_nil l:
  (forall t:term, ~ In t l)-> l = [].
Proof.
  intros. induction l. auto.
  assert(H2:= H a). 
  apply not_in_cons in H2. destruct H2. now exfalso.
Qed.

(*
if a lTerm is empty, then for all different term, it is not in that lTerm.
*)
Lemma nil_forall_not_In{X:Type} l:
  forall t:X, l=[] -> ~ In t l.
Proof.
  intros. destruct l. auto. inversion H.
Qed.

(*
NReducing two same list appended result in empty.
*)
Lemma NReducing'_listsame:forall(l:list term),
  NReducing'(l++l) = [].
Proof.
  intros. apply forall_Not_In_nil.
  intros. 
  assert(H:=same_list_even_el l t).
  assert(H0:= count_NReducing'_1_0 (l++l) t).
  destruct (Even_Odd_dec (count_occ term_beq_syn_dec (l ++ l) t)).
  - apply count_occ_not_In in H0. auto.
  - destruct H. destruct o. rewrite H in H1. lia.
Qed.
  