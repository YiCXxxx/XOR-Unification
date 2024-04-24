(*
This file mainly stores some useful Lemma for lists
Everything is pretty trivial
Nothing very important
Detailed comment omit
*)

From XORUnif Require Export Order.



Lemma rev_nil:forall(l:list term),
  rev l = [] <-> l = [].
Proof.
  intros;split;intros;simpl;auto.
  - induction l. auto. apply list_lenght_correct in H. simpl in H.
    rewrite length_nat_app in H. simpl in H.
    rewrite Nat.add_1_r in H. inversion H.
  - rewrite H. now simpl.
Qed.

Lemma rev_f_equal:forall(l1 l2:list term),
  l1 = l2 <-> rev l1 = rev l2.
Proof.
  split.
  - intro. now rewrite H.
  - generalize dependent l2. pattern l1. induction l1.
    + simpl. intros. symmetry. symmetry in H. now apply rev_nil.
    + intros l0 H. simpl in H. destruct l0. 
      -- apply list_lenght_correct in H. rewrite length_nat_app in H.
         simpl in H. rewrite Nat.add_1_r in H. inversion H.
      -- apply app_inj_tail in H. destruct H. rewrite H0. f_equal. now apply IHl1. 
Qed.

Lemma length_geq_1{X:Type}: forall (t:X)(l:list X),
  1 <= length_nat(t::l).
Proof.
  intros. induction l;simpl;lia.
Qed.

Lemma n_add_break: forall (t:term)(l1 l2:list term), 
  ~ In t l1 -> n_add t (l1++l2) = l1 ++(n_add t l2).
Proof.
  intros. induction l1;simpl.
  - auto.
  - apply not_in_cons in H. destruct H. rewrite term_beq_syn_sym.
    apply term_beq_syn_false_iff in H. rewrite H. f_equal. 
    now apply IHl1 in H0.
Qed. 

Lemma n_add_same:forall(t:term)(l:list term),
  ~ In t l -> n_add t (n_add t l) = l.
Proof.
  intros. apply n_add_not_In in H as H1. rewrite H1. 
  apply n_add_break with t l [t] in H. rewrite H. simpl.
  rewrite term_beq_syn_relf. now rewrite app_nil_end.
Qed.


Lemma n_add_notIn_exists:forall(t:term)(tl:list term),
  ~ In t tl -> exists (l1 l2:list term), n_add t tl = l1 ++ t :: l2.
Proof.
  intros. apply n_add_not_In in H. rewrite H. exists tl. exists nil. now simpl.
Qed.


Lemma In_exists:forall(t:term)(l:list term),
  In t l -> exists (l1 l2:list term), l = l1 ++ t:: l2.
Proof.
  intros. induction l.
  - inversion H.
  - inversion H.
    + exists nil. exists l. now rewrite H0.
    + apply IHl in H0. destruct H0. destruct H0. rewrite H0.
      exists (a::x). exists x0. now simpl.
Qed.



Lemma remove_app_tail:forall(t1 t2: term)(l:list term),
  t1 <> t2 -> remove t1 (l++[t2]) = (remove t1 l) ++ [t2].
Proof.
  intros. apply term_beq_syn_false_iff in H. induction l.
  - simpl. rewrite term_beq_syn_sym in H. now rewrite H.
  - simpl. destruct(term_beq_syn a t1);auto. simpl. now f_equal.
Qed. 

Lemma neq_nadd_remove_homo:forall(t1 t2: term)(l:list term),
  t1 <> t2 -> n_add t1 (remove t2 l) = remove t2 (n_add t1 l).
Proof.
  induction l.
  - intros. simpl. apply term_beq_syn_false_iff in H. now rewrite H.
  - intros. firstorder. simpl. destruct (term_beq_syn a t2) eqn:H1; destruct (term_beq_syn a t1) eqn:H2. 
    -- apply term_beq_syn_true_iff in H1. apply term_beq_syn_true_iff in H2.
       rewrite H2 in H1. now apply H in H1.
    -- simpl. now rewrite H1.
    -- simpl. now rewrite H2.
    -- simpl. rewrite H1. rewrite H2. f_equal. auto.
Qed.  


Lemma NReducing'_notIn_preserve:forall(t:term)(l:list term),
  ~ In t l -> ~ In t (NReducing' l).
Proof.
  intros. intro. apply H. clear H. induction l.
  - simpl. auto.
  - destruct(term_beq_syn_dec a t). 
    + rewrite e. now left.
    + right. apply IHl. simpl NReducing' in H0. destruct (In_dec a (NReducing' l)).
      -- apply n_add_In in i. rewrite i in H0. clear IHl i. remember (NReducing' l) as ll.
         clear Heqll. assert(H:=not_In_remove t a ll).
         assert(In t (remove a ll)-> In t ll).
         ++ intro. destruct(In_dec t ll). auto. firstorder.
         ++ apply H1. auto.
      -- apply n_add_not_In in n0. rewrite n0 in H0. apply in_app_or in H0. destruct H0.
         auto. inversion H. now apply n in H0. inversion H0.
Qed.

Lemma NReducing'_exists_hd:forall(t:term)(l:list term),
  ~ In t l -> exists (ll:list term), NReducing' (t::l) = ll ++ [t].
Proof.
  intros. induction l.
  - simpl. now exists nil.
  - apply not_in_cons in H. destruct H. apply IHl in H0 as H01. destruct H01. 
    simpl. destruct (In_dec a (NReducing' l));simpl.
    + simpl in H0. apply n_add_In in i. rewrite i. 
      assert(H2:= neq_nadd_remove_homo t a (NReducing' l) H).
      rewrite H2. simpl in H1. rewrite H1. simpl. rewrite remove_app_tail. 
      now exists (remove a x). intro. symmetry in H1. now apply H.
    + apply n_add_not_In in n as n1. rewrite n1. cut (~ In t (NReducing' l ++ [a])).
      -- intros. apply n_add_not_In in H2. rewrite H2. now exists (NReducing' l ++ [a]).
      -- apply ListUtil.notin_app. split. now apply NReducing'_notIn_preserve in H0.
         intro. inversion H2. symmetry in H3. now apply H in H3. inversion H3.
Qed.

Lemma NReducing'_hd_tail:forall(t:term)(l:list term),
  ~ In t l -> NReducing' (t::l) = (NReducing' l) ++ [t].
Proof.
  intros. induction l.
  - simpl. auto.
  - apply not_in_cons in H. destruct H. apply IHl in H0 as H01. 
    simpl. destruct (In_dec a (NReducing' l));simpl.
    + simpl in H0. apply n_add_In in i. rewrite i. 
      assert(H2:= neq_nadd_remove_homo t a (NReducing' l) H).
      rewrite H2. simpl in H01. rewrite H01. simpl. rewrite remove_app_tail. 
      auto. intro. symmetry in H1. now apply H.
    + apply n_add_not_In in n as n1. rewrite n1. cut (~ In t (NReducing' l ++ [a])).
      -- intros. apply n_add_not_In in H1. rewrite H1. auto.
      -- apply ListUtil.notin_app. split. now apply NReducing'_notIn_preserve in H0.
         intro. inversion H1. symmetry in H2. now apply H in H2. inversion H2.
Qed.

Lemma NReducing'_tail_hd:forall(t:term)(l:list term),
  ~ In t l -> NReducing' (l++[t]) = t::(NReducing' l).
Proof.
  intros. induction l.
  - simpl. auto.
  - apply not_in_cons in H. destruct H. apply IHl in H0 as H1. 
    simpl. rewrite H1. simpl. apply term_beq_syn_false_iff in H. rewrite H. auto.
Qed.

Lemma NReducing'_nadd_tail:forall(t:term)(l:list term),
  ~ In t l -> n_add t (NReducing' (l ++ [t])) = NReducing' l.
Proof.
  intros. apply NReducing'_tail_hd in H. rewrite H. 
  simpl. now rewrite term_beq_syn_relf.
Qed.

Lemma rev_tail:forall(t:term)(l:list term),
  rev(l++[t]) = t::(rev l).
Proof.
  intros. induction l;simpl.
  - auto.
  - rewrite IHl. now simpl. 
Qed.


Lemma remove_In:forall(t:term)(l l':list term),
  In t l -> remove t (l ++ l') = (remove t l) ++ l'.
Proof.
  intros. induction l. inversion H. inversion H.
  - simpl. rewrite H0. rewrite term_beq_syn_relf. auto.
  - apply IHl in H0. simpl. destruct (term_beq_syn a t).
    + auto.
    + simpl. now f_equal.
Qed.

Lemma remove_Not_In:forall(t:term)(l l':list term),
  ~ In t l -> remove t (l ++ l') = l ++ (remove t l').
Proof.
  intros. induction l;simpl. auto. apply not_in_cons in H.
  destruct H. apply IHl in H0. apply not_eq_sym in H. apply term_beq_syn_false_iff in H.
  rewrite H. now f_equal.
Qed.


Lemma rev_remove:forall(t:term)(l:list term),
  sort_term (rev (remove t l)) = sort_term (remove t (rev l)).
Proof.
  intros. apply Permutation_sort_same.
  rewrite <- Permutation_rev. apply Permutation_remove_sym. 
  apply Permutation_rev.
Qed.
(* 
Lemma in_const_sort: forall(n:nat) (l:list term),
  In (C n) (sort_constterm(C n::l)).
Proof.
  intros. unfold sort_constterm.
  simpl. 
Admitted.

Lemma In_var_term_sort: forall(v:var) (l:list term),
  In (V v) (sort_varterm(V v::l)).
Proof.
  intros. unfold sort_constterm.
  simpl. 
Admitted. 


Lemma sort_remove:forall(t:term)(l:list term),
  sort_term (remove t l) = remove t (sort_term l).
Proof.
  intros. induction l.
  - simpl. auto.
  - simpl. destruct (term_beq_syn a t) eqn:H.
    + unfold sort_term. destruct a.
      -- unfold sort_varterm. simpl. cut (sort_constterm l = remove t (sort_constterm (C n :: l))).
         ++ intros. apply term_beq_syn_true_iff in H. rewrite H0. rewrite <- H.
            assert(In (C n) (sort_constterm ((C n) :: l))). {apply in_const_sort. } 
            assert(H2:= remove_In (C n) (sort_constterm (C n :: l)) 
            (var_termconst (sort_var (Vterm_var (lt_var l)))) H1).
            rewrite H2. auto.
         ++ apply term_beq_syn_true_iff in H. rewrite <- H. 
Admitted.
         *)
Lemma Permutation_cons_rev:forall (t:term)(l1 l2:list term),
  Permutation (t::l1) (t::l2) -> Permutation l1 l2.
Proof.
  intros. assert(H1:= Permutation_remove_sym (t::l1) (t::l2) t H). simpl in H1.
  now rewrite term_beq_syn_relf in H1.
Qed.

Lemma Permutation_app_head_rev: forall (l tl tl' : list term), 
  Permutation (l++tl) (l++tl') -> Permutation tl tl'.
Proof.
  intros. induction l. now simpl in H. 
  assert(H1:= Permutation_remove_sym ((a :: l) ++ tl) ((a :: l) ++ tl') a H).
  simpl in H1. rewrite term_beq_syn_relf in H1. firstorder. 
Qed.

Lemma Permutation_app_tail_rev: forall (l tl tl' : list term), 
  Permutation (tl++l) (tl'++l) -> Permutation tl tl'.
Proof.
  intros. assert(H1:=Permutation_app_comm tl l).
  assert(H2:=Permutation_app_comm tl' l).
  assert(Permutation (l ++ tl) (l ++ tl')).
  - apply Permutation_sym in H1. rewrite H1. rewrite <- H2. auto.
  - now apply Permutation_app_head_rev in H0.
Qed.

Lemma Permutation_app_tail_rev_nat: forall (l tl tl' : list nat), 
  Permutation (tl++l) (tl'++l) -> Permutation tl tl'.
Proof.
  apply Permutation_app_inv_r.
Qed.

Lemma Permutation_app_tail_rev_var: forall (l tl tl' : list var), 
  Permutation (tl++l) (tl'++l) -> Permutation tl tl'.
Proof.
  apply Permutation_app_inv_r.
Qed.