(* 

This file mainly handles the data structure for lTerm and the equivalence relations 
between two lTerms and some important Theorem between transformations.

- lTerms
  * Incentives: We are designing this data structure so that it is easier to handle the term when rewriting
  * The intuition is, break every oplus and put every subterm into a list
    ** examples 1: C 1 +' V v +' V v' -> [C 1; V v; V v']
    ** examples 2: C 1 +' (V v +' V v') -> [C 1; V v +' V v']

- equivalence relations between lTerms,
  * the lTerm equvalence reltaions suppose to captures the same equivalence relations their term form captures,
    so the equivalence relations here should includes the four axioms for term eqv.
    ** Associativity and Commutative: lr_perm
    ** Unity: lr_T0
    ** Nilepotency: lr_N
    
    Then also the equivalence relations
    ** lr_trans
    ** lr_sym
    ** lr_relf

    Also the congruence relations
    ** lr_compat

    Then the special part for list representations:
    ** lr_eqv_add1
    ** lr_oplus
  
- Theorem term_eqv_ok: forall (t1 t2:term), 
  (term_to_lTerm t1) =l= (term_to_lTerm t2) <-> t1 == t2.

  Theorem lTerm_eqv_ok: forall (l1 l2:list term),
  lTerm_eqv l1 l2 <-> lTerm_to_term l1 == lTerm_to_term l2.
*)

From XORUnif Require Export Permutation.

Notation lTerm := (list term).

(*
Functions transforming term to lTerm and back
*)
Fixpoint term_to_lTerm (t:term):lTerm:=
  match t with
  |t1 +' t2 => (term_to_lTerm t1) ++ (term_to_lTerm t2)
  |_ => [t]
  end.

Fixpoint lTerm_to_term (tl:lTerm):term:=
  match tl with
  | [] => T0
  | t::tl' => t +' (lTerm_to_term tl')
  end.

(*
Some Utilities about the transformation functions
*)
Lemma lTerm_to_term_split: forall (tl1 tl2:lTerm),
  lTerm_to_term(tl1 ++ tl2) == lTerm_to_term tl1 +' lTerm_to_term tl2.
Proof.
  intros. induction tl1.
  - simpl. now rewrite eqvU.
  - simpl. rewrite eqvA. now apply Oplus_compat.
Qed.


(*
Some simple lemma about lterm
*)
Lemma lTerm_eqv_t_singleton: forall (t:term),
  t == lTerm_to_term [t].
Proof.
  intros. induction t;simpl;try rewrite eqvU';apply eqv_ref.
Qed.

Lemma listTransCorrect_t: forall (t:term),
  t == lTerm_to_term (term_to_lTerm t).
Proof.
  intros. induction t; simpl; try now rewrite eqvU'.
  rewrite lTerm_to_term_split. now rewrite IHt1, IHt2 at 1.
Qed.


(*
The equivalence relations between two lTerm
*)
Inductive lTerm_eqv: lTerm -> lTerm -> Prop:=
|lr_T0 ll lr: lTerm_eqv (ll++lr) (ll++T0::lr)
|lr_eqv_add1 x y l1 l2: x == y -> lTerm_eqv (l1++x::l2) (l1++y::l2)
|lr_N l: lTerm_eqv (l++l) [T0]
|lr_perm x y: Permutation x y -> lTerm_eqv x y
|lr_compat l1 l2 l3 l4: lTerm_eqv l1 l2->lTerm_eqv l3 l4
                              -> lTerm_eqv (l1++l3) (l2++l4)
|lr_trans l1 l2 l3: lTerm_eqv l1 l2 -> lTerm_eqv l2 l3->lTerm_eqv l1 l3
|lr_sym l1 l2: lTerm_eqv l1 l2 -> lTerm_eqv l2 l1
|lr_relf l1: lTerm_eqv l1 l1
|lr_oplus t1 t2: lTerm_eqv [t1 +' t2] [t1;t2].
Notation "x =l= y" := (lTerm_eqv x y) (at level 70).



(*
This is the Nilepotency add function needed later,
It takes in an term a and n_add it into lTerm x,
if a is already in x then remove a instead,
if a is not in x then add a in.
*)
Fixpoint n_add (a:term) (x:lTerm) : lTerm :=
    match x with
    | nil => a :: nil
    | a1 :: x1 =>
        if term_beq_syn a1 a
            then x1
            else a1 :: n_add a x1
    end.

(*
Some simple utilities about n_add
*)
Lemma n_add_not_In: forall (t:term)(tl:lTerm),
    ~ In t tl -> n_add t tl = app tl [t].
Proof. 
    intros. induction tl. now simpl.
    simpl. destruct (term_beq_syn a t) eqn: H1.
    - apply term_beq_syn_true_iff in H1. rewrite H1 in H.
      exfalso. apply H. simpl; now left. 
    - assert(~ In t tl). intro. apply H. now right.
      apply IHtl in H0. now rewrite H0.
Qed.  

Lemma n_add_In: forall (t:term)(tl:lTerm),
    In t tl -> n_add t tl = remove t tl.
Proof.
  intros. induction tl. inversion H.
  inversion H. simpl. rewrite H0. now rewrite term_beq_syn_relf.
  apply IHtl in H0. simpl. destruct (term_beq_syn a t) eqn:H1.
  - easy. - now rewrite H0.
Qed.


(*
Some different data structures for lTerm_eqv
*)
Lemma listTransCorrect_lr_term: forall (t:term),
  [t] =l= (term_to_lTerm t).
Proof.
  induction t;simpl;try apply lr_relf. 
  assert (a:= lr_compat [t1](term_to_lTerm t1)
  [t2](term_to_lTerm t2)IHt1 IHt2).  simpl in a.
  apply lr_trans with [t1 ; t2]. apply lr_oplus. easy.
Qed.
  
Lemma listTransCorrect_lr: forall (tl:lTerm),
  tl =l= (term_to_lTerm(lTerm_to_term tl)).
Proof.
  intros. induction tl.
  - simpl. assert(a:=lr_T0 [] []). now simpl in a.
  - simpl. assert(b:=lr_compat [a] (term_to_lTerm a) 
    tl (term_to_lTerm (lTerm_to_term tl))). apply b.
    + apply listTransCorrect_lr_term.
    + easy.
Qed.


Lemma In_dec : forall (a:term) (x:list term), {In a x} + {~ In a x}.
Proof.
    induction x.
    - simpl. right. easy.  
    - destruct IHx.
        + left. simpl. now right.
        + destruct (term_beq_syn a a0) eqn: H. left. 
          simpl. left. now apply term_beq_syn_true_iff in H.
          right. intro. inversion H0. apply term_beq_syn_false_iff in H.
          symmetry in H1. now apply H in H1. now apply n in H1.
Qed.

(*
Some simple Utilities about remove regarding not In
*)
Lemma remove_noop: forall (t:term) (tl:list term),
  ~ In t tl-> remove t tl = tl.
Proof.
  intros. induction tl; simpl. easy.
  destruct (term_beq_syn a t) eqn:H1. exfalso; apply H.
  apply term_beq_syn_true_iff in H1. now left.
  assert(~ In t tl). intro. apply H. now right.
  apply IHtl in H0. now rewrite H0.
Qed.

Lemma not_In_remove: forall (t1 t2:term) (tl:list term),
    ~ In t1 tl -> ~ In t1 (remove t2 tl).
Proof.
  intros. induction tl. now simpl.
  intro. apply not_in_cons in H. destruct H. firstorder. apply H2.
  simpl in H0. destruct (term_beq_syn a t2) eqn:H3. now apply H1 in H0.
  inversion H0. symmetry in H4. now apply H in H4. easy.
Qed.

(*Some simple Utilities about remove and count_occ*)
Lemma count_occ_remove_neq: forall (x t:term)(tl:lTerm),
  x <> t -> 
  count_occ term_beq_syn_dec (remove t tl) x = count_occ term_beq_syn_dec tl x.
Proof.
  intros. induction tl;simpl. auto.
  destruct (term_beq_syn a t) eqn:J;destruct(term_beq_syn_dec a x);auto.
  - apply term_beq_syn_true_iff in J. subst. exfalso. now apply H.
  - rewrite count_occ_cons_eq;auto.
  - simpl. destruct(term_beq_syn_dec a x);auto. exfalso;subst. now apply n.
Qed.

Lemma count_occ_minus_1:forall(x:term)(tl:lTerm)(n:nat),
  count_occ term_beq_syn_dec tl x = n ->
  count_occ term_beq_syn_dec (remove x tl) x = n-1.
Proof.
  intros. induction tl;simpl in *. rewrite H. auto. lia.
  destruct (term_beq_syn_dec a x). destruct (term_beq_syn a x)eqn:K;subst;try lia.
  apply term_beq_syn_false_iff in K. exfalso; now apply K. destruct (term_beq_syn a x)eqn:n1.
  apply term_beq_syn_true_iff in n1. exfalso;subst. now apply n0. simpl. 
  destruct (term_beq_syn_dec a x). exfalso;subst. now apply n0. firstorder.
Qed.

Lemma count_occ_plus_1:forall(x:term)(tl:lTerm)(n:nat),
  count_occ term_beq_syn_dec (remove x tl) x = n
  ->
  count_occ term_beq_syn_dec tl x = S n \/ count_occ term_beq_syn_dec tl x = 0.
Proof.
  intros. induction tl; simpl in *. now right. 
  destruct (term_beq_syn_dec a x). 
  - subst. rewrite term_beq_syn_relf in *. left. auto.
  - destruct (term_beq_syn a x) eqn:H1. apply term_beq_syn_true_iff in H1. subst. 
    exfalso; now apply n0. simpl in H. destruct(term_beq_syn_dec a x). subst.
    exfalso; now apply n0. apply IHtl in H. auto.
Qed.

Lemma count_occ_remove_0:forall(x t:term)(tl:lTerm),
  count_occ term_beq_syn_dec tl x = 0 ->
  count_occ term_beq_syn_dec (remove t tl) x = 0.
Proof.
  intros. induction tl. auto. simpl in *. destruct (term_beq_syn_dec a x);subst.
  inversion H. destruct (term_beq_syn a t)eqn:H2. apply term_beq_syn_true_iff in H2;subst.
  auto. simpl. destruct (term_beq_syn_dec a x). subst. exfalso;now apply n. firstorder.
Qed.

Lemma count_occ_remove_0_rev:forall(x t:term)(tl:lTerm),
  count_occ term_beq_syn_dec (remove t tl) x = 0 ->
  count_occ term_beq_syn_dec tl x = 1 \/ count_occ term_beq_syn_dec tl x = 0.
Proof.
  intros. induction tl;simpl in *. now right.
  destruct (term_beq_syn_dec a x);destruct (term_beq_syn a t) eqn:H1;subst.
  left. lia. simpl in *. destruct (term_beq_syn_dec x x). lia. exfalso;now apply n.
  apply term_beq_syn_true_iff in H1. subst. now right. simpl in *. destruct (term_beq_syn_dec a x);
  subst. exfalso; now apply n. apply IHtl in H. auto.
Qed.

Lemma count_occ_eq_dec:forall(x:term)(tl:lTerm),
S (count_occ term_beq_syn_dec (remove x tl) x) = count_occ term_beq_syn_dec tl x \/
count_occ term_beq_syn_dec tl x = 0.
Proof.
  intros. induction tl. auto. destruct IHtl;simpl in *.
  - destruct (term_beq_syn_dec a x);simpl;destruct (term_beq_syn a x) eqn:H1.
    + now left.
    + rewrite e in H1. now rewrite term_beq_syn_relf in H1.
    + apply term_beq_syn_true_iff in H1. subst. exfalso;now apply n.
    + simpl. destruct (term_beq_syn_dec a x). subst. exfalso;now apply n.
      now left.
  -  rewrite H in *. destruct(term_beq_syn a x)eqn:H1. destruct (term_beq_syn_dec a x);simpl;subst.
    + rewrite H. now left.
    + now right.
    + destruct(term_beq_syn_dec a x). rewrite e in H1. now rewrite term_beq_syn_relf in H1. now right.
Qed.


Lemma Permutation_remove_sym: forall(tl1 tl2:list term)(t:term),
  Permutation tl1 tl2 -> Permutation (remove t tl1) (remove t tl2).
Proof.
  intros. induction H. 
    - simpl. constructor.
    - simpl. destruct(term_beq_syn). easy. constructor. easy.
    - simpl. destruct(term_beq_syn y t)eqn:Hyt; destruct(term_beq_syn x t)eqn:Hxt.
      + apply term_beq_syn_true_iff in Hyt, Hxt. rewrite Hyt,Hxt. apply Permutation_relf.
      + apply Permutation_relf.
      + apply Permutation_relf.
      + constructor.
    - apply Permutation_trans with (remove t l');easy.
Qed. 

Lemma count_occ_In_remove:forall(t:term)(tl:lTerm),
  In t tl -> 
  count_occ term_beq_syn_dec tl t = S (count_occ term_beq_syn_dec (remove t tl) t).
Proof.
  intros. destruct(count_occ_eq_dec t tl). auto. assert(K:= count_occ_In term_beq_syn_dec tl t).
  inversion K. apply H1 in H. rewrite H0 in H. lia.
Qed.

Lemma Permutation_remove_sym_In_rev: forall(tl1 tl2:list term)(t:term),
  In t tl1 -> In t tl2 ->
  Permutation (remove t tl1) (remove t tl2) -> Permutation tl1 tl2.
Proof.
  intros. assert (J:=Permutation_count_occ term_beq_syn_dec tl1 tl2). inversion J.
  apply H3. clear J H2 H3.
  assert (J:=Permutation_count_occ term_beq_syn_dec (remove t tl1)(remove t tl2)).
  inversion J. intros. clear J H3. assert(H3:= H2 H1 x). apply count_occ_In_remove in H.
  apply count_occ_In_remove in H0. clear H2. destruct (term_beq_syn_dec t x).
  - subst. rewrite H0. rewrite H. now f_equal.
  - apply not_eq_sym in n.
    apply (count_occ_remove_neq _ _ tl1) in n as J.
    apply (count_occ_remove_neq _ _ tl2) in n as J1. congruence.
Qed.

Lemma Permutation_inv: forall (tl1 tl2:list term) (t:term), 
  Permutation (t :: tl1) (t :: tl2) -> Permutation tl1 tl2.
Proof.
  intros. assert (a:= Permutation_remove_sym (t :: tl1) (t :: tl2) t H).
  simpl in a. now rewrite term_beq_syn_relf in a.
Qed.

Lemma Permutation_remove_asym: forall(tl1 tl2: list term)(t:term),
  Permutation (t::tl1) tl2 -> Permutation tl1 (remove t tl2).
Proof.
  intros. assert(b:= Permutation_In (t :: tl1) tl2 t H). 
  assert (In t (t :: tl1)). now left. apply b in H0.
  induction tl2.
  - apply Permutation_length in H. simpl in H. inversion H.
  - inversion H0. rewrite H1. simpl. rewrite term_beq_syn_relf.
    rewrite H1 in H. now apply Permutation_inv in H.
    assert (c:=bool_dec (term_beq_syn t a) true). destruct c.
    + apply term_beq_syn_true_iff in e. rewrite e in *. simpl. rewrite term_beq_syn_relf.
      now apply Permutation_inv in H.
    + apply not_true_is_false in n. 
      assert (d:= Permutation_remove_sym (t :: tl1) (a :: tl2) t H).
      simpl remove at 1 in d. now rewrite term_beq_syn_relf in d.
Qed.

Lemma remove_add_notIn: forall(tl:list term)(t:term),
  ~ In t tl -> t::(remove t tl) = t::tl.
Proof.
  intros. apply remove_noop in H as H1. now rewrite H1.
Qed.

Lemma remove_add_In_lr: forall(tl:list term)(t:term),
  In t tl -> 
    lTerm_to_term  (t::(remove t tl)) == lTerm_to_term tl.
Proof.
  intros. induction tl;inversion H. 
  rewrite H0. simpl. now rewrite term_beq_syn_relf.
  apply IHtl in H0 as H1. simpl. destruct(term_beq_syn a t)eqn:Hat.
  + apply term_beq_syn_true_iff in Hat. now rewrite Hat.
  + simpl. rewrite <- H1. simpl. rewrite <- eqvA. rewrite <- eqvA.
    assert(t +' a == a +' t). apply eqvC. now rewrite H2. 
Qed.


Lemma Permutation_eqv: forall (x y : list term),
  Permutation x y -> lTerm_to_term x == lTerm_to_term y.
Proof.
  intro x. induction x.
  - intros. apply Permutation_nil_l in H. now rewrite H.
  - intros. apply Permutation_remove_asym in H as H1. apply IHx in H1.
    simpl. destruct(In_dec a y).
    + apply remove_add_In_lr in i. simpl in i. rewrite <- i.
      apply Oplus_compat;easy.
    + assert(b:= Permutation_In (a :: x) y a H). assert(In a (a :: x)).
      now left. now firstorder.
Qed.


Lemma n_add_remove_eqv: forall (tl:list term) (t:term),
  In t tl -> lTerm_eqv (n_add t tl) (remove t tl).
Proof.
  intros. apply n_add_In in H. rewrite H. constructor. 
  apply Permutation_relf.
Qed.

Lemma lTerm_eqv_N: forall (tl:list term) (t:term),
  lTerm_eqv (t :: t :: tl) tl.
Proof.
  intros. assert (a:=lr_N [t]). simpl in a. 
  assert(b:=lr_compat [t; t] [T0] tl tl a). simpl in b. 
  assert(lTerm_eqv (T0::tl) tl). assert(c:=lr_T0 [] tl). simpl in c.
  now apply lr_sym. assert(c:= lr_trans (t :: t :: tl) (T0::tl) tl).
  apply c. apply b. apply lr_relf. easy.
Qed.  

Lemma n_add_cons_eqv: forall (tl:list term) (t:term),
  lTerm_eqv (n_add t tl) (t::tl).
Proof.
  intros. destruct (In_dec t tl).
  + apply n_add_In in i as H. rewrite H. apply lr_sym.
    induction tl.
    - simpl in *. inversion H.
    - inversion i. rewrite H0. simpl. rewrite term_beq_syn_relf. apply lTerm_eqv_N. 
      simpl. destruct (term_beq_syn a t) eqn:H1.
      ++ apply term_beq_syn_true_iff in H1. rewrite H1. apply lTerm_eqv_N.
      ++ assert(lTerm_eqv (t :: a :: tl) (a :: t :: tl)).
         constructor. constructor. simpl in H. rewrite H1 in H. injection H.
         intro. apply IHtl in H0. apply lr_trans with (a :: t :: tl). easy.
         assert(c:= lr_compat [a] [a] (t :: tl)(remove t tl)). simpl in c. apply c.
         constructor. constructor. constructor. easy. easy.
  + apply n_add_not_In in n. rewrite n. constructor. 
    assert (t :: tl = [t]++tl)%list. now simpl. rewrite H.
    apply Permutation_app_comm.
Qed.


Lemma lTerm_eqv_relf: forall (tl:list term),
  lTerm_eqv tl tl.
Proof.
  intros. constructor. apply Permutation_relf.
Qed.

Lemma lTerm_eqv_cons: forall (tl:list term) (t:term),
  lTerm_eqv tl tl -> lTerm_eqv (t::tl) (t::tl).
Proof.
  intros. apply lTerm_eqv_relf.
Qed.


Lemma list_eqv_rev: forall (lt:list term),
  lTerm_eqv lt (rev lt).
Proof.
  intros. induction lt;simpl.
  - constructor. constructor.
  - apply lr_trans with (lt ++ [a]).
    + constructor. now assert (H:=Permutation_cons_append lt a).
    + apply lr_compat;auto. constructor; constructor;constructor.
Qed.



Lemma lTerm_eqv_cons_compat: forall (tl1 tl2:list term) (t:term),
  lTerm_eqv tl1 tl2 -> lTerm_eqv (t::tl1) (t::tl2).
Proof.
  intros. induction H;assert(a:= lr_compat [t] [t]); 
    apply a; try apply lTerm_eqv_relf.
  - apply lr_T0.
  - now apply lr_eqv_add1.
  - apply lr_N.
  - now constructor.
  - clear a. assert(a:=lr_compat l1 l2 l3 l4). now apply a.
  - now apply lr_trans with l2.
  - now apply lr_sym.
  - apply lr_oplus.
Qed.



Lemma listEqv_eqv_sound: forall (l1 l2:list term),
  lTerm_eqv l1 l2 -> lTerm_to_term l1 == lTerm_to_term l2.
Proof.
  intros. induction H.
    + assert(c:= lTerm_to_term_split ll lr). rewrite c.
      assert(d:= lTerm_to_term_split ll (T0::lr)). rewrite d.
      simpl. now rewrite eqvU.
    + assert(c:= lTerm_to_term_split l1 (x::l2)). rewrite c.
      assert(d:= lTerm_to_term_split l1 (y::l2)). rewrite d.
      apply Oplus_compat. easy. simpl. now apply Oplus_compat.
    + assert(c:= lTerm_to_term_split l l). rewrite c. 
      simpl. rewrite eqvN. now rewrite eqvU.
    + now apply Permutation_eqv.
    + rewrite lTerm_to_term_split. rewrite lTerm_to_term_split.
      now rewrite IHlTerm_eqv1,IHlTerm_eqv2.
    + now rewrite IHlTerm_eqv1.
    + now rewrite IHlTerm_eqv.
    + easy.
    + simpl. rewrite eqvA. easy.
Qed.

Lemma lTerm_eqv_Sound: forall (t1 t2:term), 
  t1 == t2 -> lTerm_eqv (term_to_lTerm t1) (term_to_lTerm t2).
Proof.
  intros. induction H;simpl.
  - constructor. rewrite app_assoc. apply Permutation_relf.
  - constructor. apply Permutation_app_comm.
  - assert(a:=lr_T0 [] (term_to_lTerm x)). simpl in a. 
    now apply lr_sym.
  - apply lr_N.
  - constructor. apply Permutation_relf.
  - now apply lr_sym.
  - apply lr_trans with (term_to_lTerm y);easy.
  - now assert(a:=lr_compat (term_to_lTerm x) (term_to_lTerm x') 
              (term_to_lTerm y) (term_to_lTerm y') IHeqv1 IHeqv2).
Qed.

Lemma listEqv_eqv_complete: forall (l1 l2:list term),
  lTerm_to_term l1 == lTerm_to_term l2 -> lTerm_eqv l1 l2.
Proof.
  intros. apply lTerm_eqv_Sound in H. 
  assert(a:= listTransCorrect_lr l1).  
  assert(b:= listTransCorrect_lr l2).
  assert(c:= lr_trans l1 (term_to_lTerm (lTerm_to_term l1)) 
        (term_to_lTerm (lTerm_to_term l2)) a H).
  assert(d:= lr_trans l1 (term_to_lTerm (lTerm_to_term l2)) 
        l2 c). apply lr_sym in b. now apply d.
Qed.

Lemma lTerm_eqv_Complete: forall (t1 t2:term), 
  lTerm_eqv (term_to_lTerm t1) (term_to_lTerm t2) -> t1 == t2.
Proof.
    intros. assert (a:=listTransCorrect_t t1);
    assert (b:=listTransCorrect_t t2). induction H; rewrite a,b.
    + assert(c:= lTerm_to_term_split ll lr). rewrite c.
      assert(d:= lTerm_to_term_split ll (T0::lr)). rewrite d.
      simpl. now rewrite eqvU.
    + assert(c:= lTerm_to_term_split l1 (x::l2)). rewrite c.
      assert(d:= lTerm_to_term_split l1 (y::l2)). rewrite d.
      apply Oplus_compat. easy. simpl. now apply Oplus_compat.
    + assert(c:= lTerm_to_term_split l l). rewrite c. 
      simpl. rewrite eqvN. now rewrite eqvU.
    + now apply Permutation_eqv.
    + apply listEqv_eqv_sound in H, H0. rewrite lTerm_to_term_split.
      rewrite lTerm_to_term_split. now apply Oplus_compat.
    + apply listEqv_eqv_sound in H, H0. now rewrite H0 in H.
    + now apply listEqv_eqv_sound in H.
    + easy.
    + simpl. rewrite eqvA. easy.    
Qed.



(*
These are the main theorem indicating if two terms are eqv, then after transforming them into lTerm form
they are lTerm eqv.
*)
Theorem term_eqv_ok: forall (t1 t2:term), 
  (term_to_lTerm t1) =l= (term_to_lTerm t2) <-> t1 == t2.
Proof.
  split.
  - apply lTerm_eqv_Complete.
  - apply lTerm_eqv_Sound.
Qed.

Theorem lTerm_eqv_ok: forall (l1 l2:list term),
  lTerm_eqv l1 l2 <-> lTerm_to_term l1 == lTerm_to_term l2.
Proof.
  split.
  - apply listEqv_eqv_sound.
  - apply listEqv_eqv_complete.
Qed.
    
