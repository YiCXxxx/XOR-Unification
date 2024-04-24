(* 

This file mainly handles the Unifications.

The definition for problem is a pair of lTerm representing left hand side and right hand side,
e.g. C 1+'C 2 =^?V x +' V y -> ([C 1;C 2],[V x;V y])

A Definition for solved Form,
* lhs of all problem are pairwise distinct variable
* lhs and rhs, terms are disjoint
* rhs is Reduced(this is not neccessary, but will be easier to handle)

A function extract substitution from solved form and important Theorem

Theorem solved_form_sub_idpt:forall(ps:problems),
  solved_form ps -> idempotent (solved_form_to_sub ps).
  - if problems are in solved form then the substitution extracted from the problems are idempotent

Theorem solved_form_sub_solves:forall(ps:problems),
  solved_form ps -> solves_problems (solved_form_to_sub ps) ps.
  - if problems are in solved form then the substitution extracted from the problems solves the problems
  
Theorem solved_form_sub_mgu_helper:forall(ps:problems)(sb:sub),
  solved_form ps -> solves_problems sb ps -> leq_sub_xor (solved_form_to_sub ps) sb.
  - if problems are in solved form then the substitution extracted from the problems are mgu

A algorithms turing every problems in solved form if they are solvable and its proof:

Theorem rawPs_to_solvedPs_solved_form:forall(ps:problems) (ps1 ps2:problems),
  steps (measure (problems_set_ready ps)) (problems_set_ready ps) = (ps1,ps2) ->
  solved_form ps2.

*)

From XORUnif Require Export Substitution.


Lemma Reducing_lr_Ord_nil:
  Reducing_lr_Ord [] = [].
Proof. auto. Qed.


Definition problem := prod lTerm lTerm. 
Definition lhs(p:problem):= fst p.
Definition rhs(p:problem):= snd p.
Definition problems := list problem.

Definition equal_problem(p:problem):Prop:=
  lhs p =l= rhs p.

Definition apply_sub_problem (sb:sub)(p:problem):problem:=
  (lftl sb (lhs p), lftl sb (rhs p)).

Definition solves_problem(sb:sub)(p:problem):Prop:=
  equal_problem (apply_sub_problem sb p).

Definition apply_sub_problems (sb:sub)(ps:problems):problems:=
  map (apply_sub_problem sb) ps.

Definition equal_problems(ps:problems):Prop:=
  Forall equal_problem ps.

Definition solves_problems (sb:sub)(ps:problems):Prop:=
  equal_problems (apply_sub_problems sb ps).

Definition mgu(sb:sub)(ps:problems):Prop:=
  forall (sb1:sub), solves_problems sb1 ps ->
  leq_sub sb sb1.

Definition mgu_xor(sb:sub)(ps:problems):Prop:=
  forall (sb1:sub), solves_problems sb1 ps ->
  leq_sub_xor sb sb1.


Lemma lTerm_eqv_app_l:forall(lt1 lt2 lt3 :lTerm),
  lt1 =l= lt2 -> lt3 ++ lt1 =l= lt3 ++ lt2.
Proof.
  intros. apply lr_compat;auto. apply lr_relf.
Qed.

Lemma lTerm_eqv_app_r:forall(lt1 lt2 lt3 :lTerm),
  lt1 =l= lt2 -> lt1 ++ lt3 =l= lt2 ++ lt3.
Proof.
  intros. apply lr_compat;auto. apply lr_relf.
Qed.


Lemma sub_solves_ts_eqn_cons:forall(sb:sub)(p:problem)(t:term),
  solves_problem sb p ->
  solves_problem sb ((t::(lhs p)), t::(rhs p)).
Proof.
  intros. unfold solves_problem in *. simpl. assert([lft sb t] =l= [lft sb t]). constructor. apply Permutation_relf.
  unfold equal_problem. simpl.
  assert(J:=lr_compat [lft sb t] [lft sb t] (lftl sb (lhs p)) (lftl sb (rhs p)) H0 H). auto.
Qed.

Lemma sub_solves_ts_eqn_app_r:forall(sb:sub)(p:problem)(tl:lTerm),
  solves_problem sb p ->
  solves_problem sb ((tl++(lhs p)), tl++(rhs p)).
Proof.
  intros. unfold solves_problem in *. unfold equal_problem in *. simpl in *. unfold lftl in *. rewrite map_app. rewrite map_app.
  assert(map (lft sb) tl =l= map (lft sb) tl). constructor. apply Permutation_relf.
  assert(J:=lr_compat (map (lft sb) tl)(map (lft sb) tl) (lftl sb (lhs p)) (lftl sb (rhs p)) H0 H). auto.
Qed.

Lemma sub_solves_ts_eqn_app_l:forall(sb:sub)(p:problem)(tl:lTerm),
  solves_problem sb p ->
  solves_problem sb ((lhs p)++tl, (rhs p)++tl).
Proof.
  intros. unfold solves_problem in *. unfold equal_problem in *. simpl in *. unfold lftl in *. rewrite map_app. rewrite map_app.
  assert(map (lft sb) tl =l= map (lft sb) tl). constructor. apply Permutation_relf.
  assert(J:=lr_compat (lftl sb (lhs p)) (lftl sb (rhs p)) (map (lft sb) tl)(map (lft sb) tl)  H H0). auto.
Qed.

Lemma term_eqv_lft:forall(sb:sub)(t1 t2:term),
  t1 == t2 -> lft sb t1 == lft sb t2.
Proof.
  intros. induction H;simp lft; constructor;auto.
  - apply eqv_trans with (lft sb y); now apply eqv_sym.
  - apply Oplus_compat; now apply eqv_sym.
Qed.

Lemma lTerm_eqv_lftl:forall(sb:sub)(lt1 lt2:lTerm),
  lt1 =l= lt2 -> lftl sb lt1 =l= lftl sb lt2.
Proof.
  intros. unfold lftl. induction H; repeat rewrite map_app; repeat rewrite map_cons.
  - constructor;auto.
  - constructor. now apply (term_eqv_lft sb) in H.
  - constructor.
  - constructor. now apply Permutation_map.
  - apply lr_compat;auto.
  - apply lr_trans with (map (lft sb) l2);auto.
  - now apply lr_sym.
  - constructor. apply Permutation_relf.
  - simp lft. simpl. apply lr_oplus.
Qed.

Ltac ufp:= unfold solves_problem in *; unfold equal_problem in *;
     unfold apply_sub_problem in *; simpl in *.

Ltac ufps:= unfold solves_problems in *; unfold equal_problems in *;
     unfold equal_problem in *;
     unfold apply_sub_problems in *; simpl in *.

Lemma Reducing_lr_Ord_lftl_comm:forall(lt:lTerm)(sb:sub),
  lftl sb (Reducing_lr_Ord lt) =l= Reducing_lr_Ord (lftl sb lt).
Proof.
  intros. assert(H:=Reducing_lr_Ord_Correct_eqv lt). apply (lTerm_eqv_lftl sb) in H.
  apply lr_sym in H. apply lr_trans with (lftl sb lt);auto. apply Reducing_lr_Ord_Correct_eqv.
Qed.

Lemma Reducing_lr_Ord_sub_preserve:forall(p:problem)(sb:sub),
  solves_problem sb p ->
  solves_problem sb (Reducing_lr_Ord (lhs p),Reducing_lr_Ord (rhs p)).
Proof.
  intros. ufp. 
  assert(K1:=Reducing_lr_Ord_Correct_eqv (lhs p)).
  assert(K2:=Reducing_lr_Ord_Correct_eqv (rhs p)).
  apply (lTerm_eqv_lftl sb) in K1. apply (lTerm_eqv_lftl sb) in K2. 
  assert(L1:=lr_trans _ _ _ H K2). apply lr_sym in L1.
  assert(L2:=lr_trans _ _ _ L1 K1). now apply lr_sym.
Qed.


Lemma Reducing_lr_Ord_listsame:forall(lt:lTerm),
  Reducing_lr_Ord (lt ++ lt) = [].
Proof.
  intros. unfold Reducing_lr_Ord. unfold Reducing_lr. rewrite <- AReducing_lr_app.
  rewrite NReducing_listsame. auto.
Qed.

Lemma lTerm_eqv_tl_singleton:forall(tl:lTerm),
  tl =l= [lTerm_to_term tl].
Proof.
  intros. induction tl. simpl. 
  apply lTerm_eqv_ok. simpl. rewrite eqvN. apply eqv_ref.
  simpl. assert(J:=lr_trans (a::tl) (a::[lTerm_to_term tl]) [a +' lTerm_to_term tl]).
  apply J. apply lTerm_eqv_cons_compat. auto.
  apply lr_sym. apply lr_oplus.
Qed.


Lemma lTerm_eqv_same_side_nil:forall(lt1 lt2:lTerm),
  lt1 =l= lt2 <-> lt1 ++ lt2 =l= [].
Proof.
  split; intros. apply lTerm_eqv_bool_correct.
  unfold lTerm_eqv_bool in *. 
  apply term_beq_syn_list_correct. apply lTerm_eqv_Reduced_nil in H. rewrite H. auto.
  assert(J:=lTerm_eqv_app_l (lt1++lt2) nil lt1 H). apply lTerm_eqv_bool_correct in J.
  unfold lTerm_eqv_bool in J. apply term_beq_syn_list_correct in J.
  rewrite app_nil_r in J. rewrite app_assoc in J.
  rewrite Reducing_lr_Ord_idpt_rev_l in J. 
  apply lTerm_eqv_bool_correct in H. apply term_beq_syn_list_correct in H.
  rewrite Reducing_lr_Ord_listsame in J. simpl in J. apply lTerm_eqv_bool_correct.
  unfold lTerm_eqv_bool. apply term_beq_syn_list_correct. now rewrite J.
Qed.  

Lemma Reducing_lr_Ord_idpt:forall (lt:lTerm),
  Reducing_lr_Ord lt = Reducing_lr_Ord (Reducing_lr_Ord lt).
Proof.
  intros. assert(H:= Reducing_lr_Ord_idpt_rev_r nil lt). now simpl in H.
Qed.  


Lemma Permutation_In_cons_remove:forall(t:term)(lt:lTerm),
  In t lt -> Permutation lt (t :: remove t lt).
Proof.
  intros. cut (Permutation (remove t lt) (remove t (t:: remove t lt))).
  intro. apply Permutation_remove_sym_In_rev in H0;auto. now left.
  simpl. rewrite term_beq_syn_relf. apply Permutation_relf.
Qed.


(* =======================================================================================*)
(*               Start                           *)
(*         Raw Problem to Reduce Problem         *)
(*         Raw Problems to Reduce Problems       *)
(* =======================================================================================*)

Definition rawP_to_reducedP(p:problem):problem:=
  ((Reducing_lr_Ord ((lhs p) ++ (rhs p)) ),[]).

Lemma rawP_to_reducedP_sub_preserve:forall(p:problem)(sb:sub),
  solves_problem sb p ->
  solves_problem sb (rawP_to_reducedP p).
Proof.
  intros. ufp. apply Reducing_lr_Ord_sub_preserve in H. ufp.
  assert(J2:=Reducing_lr_Ord_lftl_comm (lhs p) sb). apply lr_sym in J2.
  assert(J1:=lr_trans _ _ _ J2 H).
  assert(J3:=Reducing_lr_Ord_lftl_comm (rhs p) sb). apply lr_sym in H.
  assert(J4:=lr_trans _ _ _ J1 J3). clear J1 J2 J3. 
  assert(J2:=Reducing_lr_Ord_lftl_comm (lhs p ++ rhs p) sb). 
  apply lr_trans with (Reducing_lr_Ord (lftl sb (lhs p ++ rhs p))). auto.
  assert(J1:=Reducing_lr_Ord_Correct_eqv (lftl sb (lhs p))).
  assert(J3:=lr_trans _ _ _ J1 J4). clear J1 J2. 
  assert(J1:=Reducing_lr_Ord_Correct_eqv (lftl sb (rhs p))). apply lr_sym in J1.
  assert(J2:=lr_trans _ _ _ J3 J1). clear H J4 J3 J1.
  unfold lftl in *. rewrite map_app.  apply lTerm_eqv_Reduced_nil in J2. rewrite J2.
  apply lr_relf.
Qed.

Lemma reducedP_to_rawP_sub_preserve:forall(p:problem)(sb:sub),
  solves_problem sb (rawP_to_reducedP p)
  -> solves_problem sb p.
Proof.
  intros. ufp. assert(L:= Reducing_lr_Ord_lftl_comm (lhs p ++ rhs p) sb). apply lr_sym in L.
  assert(J:=lr_trans _ _ _ L H). clear H L.
  assert(J1:=Reducing_lr_Ord_Correct_eqv ((lftl sb (lhs p ++ rhs p)))).
  assert(J2:=lr_trans _ _ _ J1 J). clear J J1. unfold lftl in *. 
  rewrite map_app in *. apply lTerm_eqv_same_side_nil. auto.
Qed.
  
Definition rawPs_to_reducedPs(ps:problems):problems:=
  map rawP_to_reducedP ps.

Lemma rawPs_to_reducedPs_sub_preserve:forall(ps:problems)(sb:sub),
  solves_problems sb ps ->
  solves_problems sb (rawPs_to_reducedPs ps).
Proof.
  intros. ufps. induction ps. simpl. auto. simpl in *. apply Forall_inv_tail in H as H1.
  apply Forall_inv in H. apply IHps in H1. constructor;auto.
  apply rawP_to_reducedP_sub_preserve in H. ufp. auto.
Qed.

Lemma reducedPs_to_rawPs_sub_preserve:forall(ps:problems)(sb:sub),
  solves_problems sb (rawPs_to_reducedPs ps) ->
  solves_problems sb ps.
Proof.
  intros. ufps. induction ps;simpl in *. auto. apply Forall_inv_tail in H as H1.
  apply Forall_inv in H. apply IHps in H1. constructor;auto.
  apply reducedP_to_rawP_sub_preserve in H. ufp. auto.
Qed.

(* =======================================================================================*)
(*                 End                           *)
(*         Raw Problem to Reduce Problem         *)
(*         Raw Problems to Reduce Problems       *) 
(* =======================================================================================*)





(* ====================================Raw Problem========================================*)
(*         Solvable and not Solvable              *)
(*         Solvable and not Solvable preserve raw problem <-> reduced problem     *)
(* =======================================================================================*)

Fixpoint any_var_in_lTerm (eq:lTerm):bool:=
  match eq with
  |[] => false
  |t::eq' => match t with
            |V _ => true
            |_ => any_var_in_lTerm eq'
  end end.

Fixpoint a_var_in_lTerm(eq:lTerm):option var:=
  match eq with 
  |[] => None 
  |t::eq' => match t with 
            |V v => Some v
            |_ => a_var_in_lTerm eq'
  end end.


Lemma a_var_in_lTerm_In:forall (eq:lTerm)(v:var),
  a_var_in_lTerm eq = Some v -> In (V v) eq.
Proof.
  intros. induction eq.
  - inversion H.
  - simpl in H. destruct a.
    + apply IHeq in H. now right.
    + left. now inversion H. 
    + apply IHeq in H. now right.
Qed.

Definition rd_eqv_bool (t1 t2:lTerm):bool:=
  lTerm_eqv_bool t1 t2.

Definition lTerm_solvable_bool(eq:lTerm):bool:=
  orb (rd_eqv_bool eq []) (any_var_in_lTerm eq).

Definition p_solvable_bool(p:problem):bool:=
  lTerm_solvable_bool (fst (rawP_to_reducedP p)).

Definition nil_list{X:Type} (l:list X):bool:=
  match l with
  |[] => true
  |_ => false
  end.


Lemma Reduced_remove_simpl:forall(x x0:lTerm)(v:var),
  Reduced_Ord (x ++ V v :: x0) -> (remove (V v) (x ++ V v :: x0)) = x ++ x0.
Proof.
  intros. inversion H;subst. inversion H0;subst. apply NReduced_NoDup in H3 as J3.
  apply NoDup_remove_2 in J3 as J4. apply ListUtil.notin_app in J4.
  destruct J4. rewrite remove_Not_In;auto. simpl. destruct (beq_var v v)eqn:K;auto.
  rewrite beq_var_refl in K. inversion K.
Qed.



Definition not_solvable_problem(p:problem):Prop:=
  forall sb:sub, ~ solves_problem sb p.

Lemma any_var_in_lTerm_false_sub_noop:forall(lt:lTerm)(sb:sub),
  Reduced_Ord lt ->
  any_var_in_lTerm lt = false ->
  lftl sb lt = lt.
Proof.
  intros. induction lt. auto. destruct a.
  - unfold lftl. rewrite map_cons. simp lft. f_equal. unfold lftl in IHlt.
    apply IHlt. now apply Reduced_Ord_remove in H. simpl in H0. auto.
  - inversion H0.
  - inversion H. inversion H1. inversion H4.
Qed.

Lemma Reduced_Ord_not_lTerm_eqv:forall(n:nat)(l:lTerm),
  n <> 0 ->  Reduced_Ord (C n :: l) -> C n :: l =l= [] -> False.
Proof.
  intros. apply Reduced_Ord_Reducing_lr_Ord in H0.
  apply lTerm_eqv_bool_correct in H1. unfold lTerm_eqv_bool in H1.
  apply term_beq_syn_list_correct in H1. rewrite H0 in H1. inversion H1.
Qed.

Lemma p_solvable_bool_false_complete:forall (p:problem),
  p_solvable_bool p = false -> not_solvable_problem p.
Proof.
  intros. unfold p_solvable_bool in H. unfold not_solvable_problem. unfold lTerm_solvable_bool in H.
  apply orb_false_iff in H. destruct H. intros. simpl in *. intro.
  ufp. remember (Reducing_lr_Ord (lhs p ++ rhs p)) as l.
  assert(J:=Reducing_lr_Ord_Correct_Reduced_Ord (lhs p ++ rhs p)). rewrite <- Heql in J.
  destruct l;simpl in *. 
  - unfold rd_eqv_bool in H. unfold lTerm_eqv_bool in H. simpl in H. inversion H.
  - destruct t.
    + apply lTerm_eqv_same_side_nil in H1. unfold lftl in H1. 
      rewrite <- map_app in H1. assert(J1:=Reducing_lr_Ord_Correct_eqv (map (lft sb) (lhs p ++ rhs p))).
      apply lr_sym in J1. assert(J2:=lr_trans _ _ _ J1 H1). 
      assert(J3:=Reducing_lr_Ord_lftl_comm (lhs p ++ rhs p) sb). unfold lftl in J3.
      assert(J4:=lr_trans _ _ _ J3 J2). rewrite <- Heql in J4. clear J1 J2 J3.
      assert(J2:=any_var_in_lTerm_false_sub_noop _ sb J). simpl in J2. firstorder.
      simp lft in H2. injection H2;intro. rewrite map_cons in J4. unfold lftl in H3.
      rewrite H3 in J4. simp lft in J4. clear H2 H3. inversion J. inversion H2.
      inversion H7;subst. 
      now assert(K:= Reduced_Ord_not_lTerm_eqv _ _ H11 J J4).
    + inversion H0.
    + inversion J. inversion H2. inversion H5.
Qed.
  
Lemma forallb_cons{X:Type}:forall(a:X)(l:list X)(f:X->bool),
  forallb f (a::l) = f a && forallb f l.
Proof. auto. Qed.




(* ========================================================================= *)
(*   Solved Form   *)
(* ========================================================================= *)

Definition single_variable_lTerm_var(tl:lTerm):option var:=
  match tl with
  |[V v] => Some v
  | _ => None
  end.

Definition single_variable_lTerm(tl:lTerm):bool:=
  match single_variable_lTerm_var tl with
  |Some _ => true
  |None => false
  end.

Fixpoint app_list_lTerm(llt:list lTerm): list term:=
  match llt with 
  |[] => []
  |lt :: llt' => lt ++ (app_list_lTerm llt')
  end.

Definition single_variable_lTerm_Prop (tl:lTerm):Prop:=
  single_variable_lTerm tl = true.

Definition disjoint_In (l1 l2:lTerm):=
  forall t:term, In t l1 -> ~ In t l2.

Definition solved_form (ps:problems):Prop:=
  NoDup (map fst ps) /\
  Forall single_variable_lTerm_Prop (map fst ps) /\
  Forall Reduced_Ord (map snd ps) /\
  disjoint_In (app_list_lTerm (map fst ps)) (app_list_lTerm (map snd ps)).



Fixpoint solved_form_to_sub (ps:problems):sub:=
  match ps with 
  |[] => id_sub
  |p::ps' => match single_variable_lTerm_var (fst p) with
             |Some v => compose_sub (singleton_sub v (lTerm_to_term (snd p))) (solved_form_to_sub ps')
             |None => solved_form_to_sub ps'
  end end.


Lemma disjoint_In_remove_e_l:forall(l1 l2:lTerm)(t:term),
  disjoint_In (t::l1) l2 -> disjoint_In l1 l2.
Proof.
  intros. unfold disjoint_In in *. intros. apply H. now right.
Qed.

Lemma disjoint_In_remove_l_l:forall(l1 l2 l3:lTerm),
  disjoint_In (l3++l1) l2 -> disjoint_In l1 l2.
Proof.
  intros. unfold disjoint_In in *. intros. apply H. apply in_app_iff. now right.
Qed.


Lemma disjoint_In_remove_e_r:forall(l1 l2:lTerm)(t:term),
  disjoint_In l1 (t::l2) -> disjoint_In l1 l2.
Proof.
  intros. unfold disjoint_In in *. intros. apply H in H0. intro. apply H0. now right.
Qed.

Lemma disjoint_In_remove_l_r:forall(l1 l2 l3:lTerm),
  disjoint_In l1 (l3++l2) -> disjoint_In l1 l2.
Proof.
  intros. unfold disjoint_In in *. intros. apply H in H0. intro. apply H0. apply in_app_iff.
  now right.
Qed.

Lemma solved_form_inv:forall(ps:problems)(p:problem),
  solved_form(p::ps) -> solved_form [p].
Proof.
  intros. inversion H. destruct H1. destruct H2. simpl in *.
  apply Forall_inv in H1. apply Forall_inv in H2. inversion H2;subst. inversion H4;subst. 
  repeat constructor;auto.
  simpl. repeat rewrite app_nil_r. clear H0 H1 H2 H4 H5 H6 H7 H8.
  unfold disjoint_In in *. intros.
  assert (L:=ListUtil.in_appl t _ (app_list_lTerm (map fst ps)) H0). apply H3 in L.
  apply ListUtil.notin_app in L. now destruct L.
Qed.

Lemma solved_form_remove:forall(ps:problems)(p:problem),
  solved_form(p::ps) -> solved_form (ps).
Proof.
  intros. unfold solved_form in *. destruct H. destruct H0. rewrite map_cons in *.
  split. apply NoDup_cons_iff in H. now destruct H. split.
  now apply Forall_inv_tail in H0. destruct H1.
  apply Forall_inv_tail in H1. split. auto.
  simpl in H2.
  apply disjoint_In_remove_l_l in H2. now apply disjoint_In_remove_l_r in H2.
Qed.

Lemma app_list_lTerm_app:forall (llt1 llt2:list lTerm),
  app_list_lTerm (llt1 ++ llt2) = app_list_lTerm llt1 ++ app_list_lTerm llt2.
Proof.
  intros. induction llt1;simpl. auto. rewrite <- app_assoc. f_equal. auto.
Qed.

Lemma solved_form_remove_middle:forall(ps1 ps2:problems)(p:problem),
  solved_form(ps1 ++ p :: ps2) -> solved_form (ps1 ++ ps2).
Proof.
  intros. induction ps1.
  - simpl in *. now apply solved_form_remove in H.
  - simpl in *. apply solved_form_remove in H as H1. apply IHps1 in H1.
    clear IHps1. inversion H. destruct H2. destruct H3. 
    constructor.
    + simpl in *. rewrite map_app in *. simpl in *.
      assert(J:= NoDup_remove_1 (fst a :: map fst ps1) (map fst ps2) (fst p)). 
      simpl in J. auto.
    + repeat split.
      -- simpl in *. rewrite map_app in *. simpl in *. constructor. now apply Forall_inv in H2.
         apply Forall_app. split;apply Forall_inv_tail in H2; apply Forall_app in H2;destruct H2.
         auto. now apply Forall_inv_tail in H5.
      -- simpl in *. rewrite map_app in *. simpl in *. constructor. now apply Forall_inv in H3.
         apply Forall_app. split;apply Forall_inv_tail in H3; apply Forall_app in H3;destruct H3.
         auto. now apply Forall_inv_tail in H5.
      -- simpl in *. repeat rewrite map_app in *. simpl in *.
         clear H H1 H0 H2 H3. unfold disjoint_In in *.
         intros. assert(In t (fst a ++ app_list_lTerm (map fst ps1 ++ fst p :: map fst ps2))).
         apply in_app_iff in H. destruct H. apply ListUtil.in_appl. auto.
         apply ListUtil.in_appr. 
         ++ clear H4. simpl in *. rewrite app_list_lTerm_app in *.
            apply in_app_iff in H. destruct H.
            * apply ListUtil.in_appl. auto.
            * apply ListUtil.in_appr. simpl. now apply ListUtil.in_appr.
         ++ apply ListUtil.notin_app. split.
            * apply in_app_iff in H. destruct H.
              ** assert(L:=ListUtil.in_appl t (fst a) 
                 (app_list_lTerm (map fst ps1 ++ fst p :: map fst ps2)) H).
                 apply H4 in L. apply ListUtil.notin_app in L. destruct L. auto.
              ** apply H4 in H0. apply ListUtil.notin_app in H0. now destruct H0.
            * apply H4 in H0. apply ListUtil.notin_app in H0. destruct H0.
              clear H4 H H0. rewrite app_list_lTerm_app in *.
              apply ListUtil.notin_app in H1. destruct H1.
              apply ListUtil.notin_app. split;auto. simpl in H0. apply ListUtil.notin_app in H0.
              destruct H0. auto.
Qed.


Lemma single_variable_lTerm_var_simpl:forall(lt:lTerm)(v:var),
  single_variable_lTerm_var lt = Some v -> lt = [V v].
Proof.
  intros. unfold single_variable_lTerm_var in H. destruct lt. inversion H.
  destruct t;try inversion H. destruct lt. inversion H1. auto. inversion H.
Qed.

Lemma not_In_Var_lTerm:forall(v:var)(ps:problems),
  ~ In (V v) (app_list_lTerm (map fst ps)) -> ~ In [V v] (map fst ps).
Proof. 
  intros. induction ps;simpl;auto.
  simpl in H. apply ListUtil.notin_app in H. destruct H. intro. destruct H1.
  apply H. rewrite H1. now left. apply IHps; auto.
Qed.

Lemma not_In_lTerm_Var:forall(v:var)(ps:problems),
  solved_form ps ->
  ~ In [V v] (map fst ps) -> ~ In (V v) (app_list_lTerm (map fst ps)) .
Proof. 
  intros. intro. apply H0. clear H0.
  induction ps;simpl in *;auto. apply in_app_iff in H1. destruct H1.
  - unfold solved_form in H. destruct H. destruct H1. 
    rewrite map_cons in H1. apply Forall_inv in H1. unfold single_variable_lTerm_Prop in H1.
    unfold single_variable_lTerm in H1. destruct (single_variable_lTerm_var (fst a)) eqn:J.
    apply single_variable_lTerm_var_simpl in J. rewrite J in *. simpl in H0. destruct H0.
    inversion H0;subst;auto. inversion H0. inversion H1.
  - right. apply IHps. now apply solved_form_remove in H. auto.
Qed.


Lemma var_of_In_tl:forall (v:var)(tl:lTerm),
  Reduced_Ord tl ->
  var_of v (lTerm_to_term tl) -> In (V v) tl.
Proof.
  intros. induction tl.
  - inversion H0.
  - simpl in *. destruct H0.
    + clear IHtl. left. destruct a. inversion H0. simpl in *. destruct(eq_dec_var v v0).
      now rewrite e. inversion H0. inversion H. inversion H1. inversion H4.
    + apply Reduced_Ord_remove in H. firstorder.
Qed.

Lemma In_tl_var_of:forall (v:var)(tl:lTerm),
  Reduced_Ord tl -> In (V v) tl
  -> var_of v (lTerm_to_term tl).
Proof.
  intros. induction tl.
  - inversion H0.
  - simpl in *. destruct H0.
    + clear IHtl. left. destruct a. inversion H0. inversion H0. simpl.
      destruct(eq_dec_var v v). auto. now apply n. inversion H. inversion H1. inversion H4.
    + apply Reduced_Ord_remove in H. firstorder.
Qed.

Lemma Not_In_tl_var_of:forall (v:var)(tl:lTerm),
  Reduced_Ord tl -> ~ In (V v) tl
  -> ~ var_of v (lTerm_to_term tl).
Proof.
  intros. induction tl. auto.
  simpl. intro. destruct H1.
  - apply not_in_cons in H0. destruct H0. destruct a. inversion H1. simpl in H1.
    destruct (eq_dec_var v v0). apply H0. now rewrite e. inversion H1.
    inversion H. inversion H3. inversion H6.
  - apply Reduced_Ord_remove in H. firstorder.
Qed.
  
Lemma var_of_In_t:forall (v:var)(t:term),
  var_of v t -> In (V v) (term_to_lTerm t).
Proof.
  intros. induction t;simpl in *. inversion H. destruct (eq_dec_var v v0).
  left. now rewrite e. inversion H. destruct H;firstorder.
  now apply ListUtil.in_appl. now apply ListUtil.in_appr.
Qed.

Lemma disjoint_In_sym:forall(lt1 lt2:lTerm),
  disjoint_In lt1 lt2 -> disjoint_In lt2 lt1.
Proof.
  intros. unfold disjoint_In in *. intros. intro. apply (H t);auto.
Qed.



Lemma solved_form_to_sub_not_in_domain:forall(ps:problems)(v:var),
  solved_form ps -> ~ In (V v) (app_list_lTerm (map fst ps)) ->
  lft (solved_form_to_sub ps) (V v) = V v.
Proof.
  intros. assert(L:=H).
  unfold solved_form in H. destruct H. destruct H1. destruct H2.
  induction ps;simpl. auto.
  destruct(single_variable_lTerm_var (fst a)) eqn:J.
  - apply solved_form_remove in L as L1. firstorder. rewrite map_cons in *. simpl in H0.
    apply ListUtil.notin_app in H0. destruct H0.
    apply Forall_inv_tail in H1. unfold compose_sub. firstorder. simp lft in *. rewrite H12.  
    destruct (eq_dec_var v v0).
    + apply single_variable_lTerm_var_simpl in J. rewrite J in H0. rewrite e in H0.
      simpl in H0. exfalso. apply H0. now left.
    + simp lft in *. assert(v0<>v).
      intro. now apply n.
      assert(J2:=update_neq id_sub v0 (lTerm_to_term (snd a)) v H14).
      simp lft in J2. 
  - rewrite map_cons in H1. apply Forall_inv in H1. unfold single_variable_lTerm_Prop in H1.
    unfold single_variable_lTerm in H1. rewrite J in H1. inversion H1.
Qed.

Lemma Forall_In: forall [A : Type] (P : A -> Prop) (l: list A)(a:A),
  Forall P l -> In a l -> P a.
Proof.
  intros. induction l. inversion H0. simpl in H0. destruct H0.
  - subst. now apply Forall_inv in H.
  - apply Forall_inv_tail in H. auto.
Qed. 

Lemma In_lTerm_list_lTerm:forall(t:term)(lt:lTerm)(llt:list lTerm),
  In t lt -> In lt llt -> In t (app_list_lTerm llt).
Proof.
  intros. induction llt. inversion H0. simpl in H0. destruct H0.
  simpl. apply ListUtil.in_appl. now rewrite H0. simpl. apply ListUtil.in_appr. auto.
Qed.

Lemma In_list_lTerm_lTerm:forall(t:term)(llt:list lTerm),
  In t (app_list_lTerm llt) -> (exists lt:lTerm, In lt llt /\ In t lt).
Proof.
  intros. induction llt. inversion H. 
  simpl in H. apply in_app_iff in H. destruct H.
  - exists a. split;auto. now left.
  - firstorder.
Qed.

Lemma solved_form_to_sub_in_domain: forall(ps:problems)(v:var),
  solved_form ps -> In (V v) (app_list_lTerm (map fst ps)) ->
  (exists lt:lTerm, (solved_form_to_sub ps v) = (lTerm_to_term lt) 
  /\ In lt (map snd ps)).
Proof.
  intros. induction ps;simpl in *. inversion H0.
  apply solved_form_remove in H as H1. firstorder. 
  apply in_app_iff in H0. destruct H0;rewrite map_cons in *.
  - apply Forall_inv in H5. unfold single_variable_lTerm_Prop in H5. unfold single_variable_lTerm in H5.
    destruct(single_variable_lTerm_var (fst a)) eqn:J. apply single_variable_lTerm_var_simpl in J.
    rewrite J in H0. inversion H0. inversion H9. subst.
    exists (snd a). split.
    + simpl in H7. unfold disjoint_In in H7. 
      assert(L:=solved_form_to_sub_not_in_domain ps v). firstorder. apply NoDup_cons_iff in H.
      destruct H. rewrite J in *. apply not_In_lTerm_Var in H;firstorder. simp lft in H10. 
      unfold compose_sub. rewrite H10. unfold singleton_sub. rewrite update_eq. auto.
    + now left.
    + inversion H9.
    + inversion H5.
  - destruct (single_variable_lTerm_var (fst a))eqn:L1;firstorder.
    unfold compose_sub. rewrite H8. exists x. apply single_variable_lTerm_var_simpl in L1.
    split. 
      -- apply noop_lft. intros. unfold Dom. intro. apply H11. 
         assert(L2:=solved_form_to_sub_not_in_domain ps x0). firstorder. 
         assert(L3:=var_of_In_tl x0 x). apply Forall_inv_tail in H6 as L5.
         assert(L4:=Forall_In Reduced_Ord (map snd ps) x L5 H9). firstorder.
         unfold disjoint_In in H7. assert(J:=In_lTerm_list_lTerm (V x0) x (map snd ps) H13 H9).
         assert(J1:=ListUtil.in_appr (V x0) (snd a) _ J).  
         apply disjoint_In_sym in H7. assert(L6:=H7 (V x0)). simpl in L6. apply L6 in J1.
         apply ListUtil.notin_app in J1. destruct J1. rewrite L1 in H14. 
         simpl in H14. assert(v0<>x0). intro. apply H14. rewrite H16. now left.
         assert(J3:=update_neq id_sub v0 (lTerm_to_term (snd a)) x0 H16). simp lft in J3.
      -- now right.
Qed.

Lemma In_Var_all_fst_ps:forall(ps:problems)(v:var),
  solved_form ps -> In (V v) (app_list_lTerm (map fst ps)) ->
  In [V v] (map fst ps).
Proof.
  intros. induction ps. inversion H0. simpl in *. apply in_app_iff in H0.
  destruct H0. left. firstorder. rewrite map_cons in *. apply Forall_inv in H1.
  unfold single_variable_lTerm_Prop in H1. unfold single_variable_lTerm in H1. 
  destruct (single_variable_lTerm_var (fst a)) eqn:J. apply single_variable_lTerm_var_simpl in J.
  rewrite J in *. inversion H0. inversion H5. auto. inversion H5. inversion H1.
  apply solved_form_remove in H. firstorder.
Qed.

Fixpoint return_snd(lt:lTerm)(ps:problems):lTerm:=
  match ps with
  |[] => lt
  |p::ps' => if term_beq_syn_list lt (fst p) 
              then (snd p)
              else return_snd lt ps'
  end.

Lemma lTerm_to_term_f_equal:forall(tl1 tl2:lTerm),
  lTerm_to_term tl1 = lTerm_to_term tl2 ->
  tl1 = tl2.
Proof.
  intros tl1. induction tl1;intros;simpl in *. destruct tl2. auto.
  - destruct t; inversion H.
  - destruct tl2. simpl in H. inversion H. simpl in H. inversion H.
    f_equal. firstorder.
Qed.

(*
Important theorem about substitution from solved form is idempotent
*)
Theorem solved_form_sub_idpt:forall(ps:problems),
  solved_form ps -> idempotent (solved_form_to_sub ps).
Proof.
  intros. assert(J:=H). unfold solved_form in H. destruct H. destruct H0.
  unfold idempotent. apply functional_extensionality.
  intros. induction ps. auto. 
  apply solved_form_remove in J as J1. firstorder. simpl.
  destruct (single_variable_lTerm_var (fst a)) eqn:L.
  - apply single_variable_lTerm_var_simpl in L. 
    destruct (In_dec (V x) (app_list_lTerm (map fst ps))).
    + apply solved_form_to_sub_in_domain in i;firstorder. 
      unfold compose_sub. rewrite H12. 
      cut (lft (singleton_sub v (lTerm_to_term (snd a))) (lTerm_to_term x0) = (lTerm_to_term x0)).
      * intros. rewrite H14. apply noop_lft. intros. unfold Dom. intro. 
        apply H16. apply var_of_In_tl in H15.
        -- assert(J:=solved_form_to_sub_not_in_domain ps x1). firstorder.
           assert(J1:=In_lTerm_list_lTerm (V x1) x0 (map snd ps)). firstorder.
           simp lft in H19. rewrite H19. 
           assert (J4:=ListUtil.in_appr (V x1) (snd a) (app_list_lTerm (map snd ps)) H18).
           apply disjoint_In_sym in H9 as J2. unfold disjoint_In in J2. 
           simpl in J2. apply J2 in J4. apply ListUtil.notin_app in J4. destruct J4.
           rewrite L in H17. unfold singleton_sub. assert(v<>x1).
           intro. apply H17. rewrite H21. now left. 
           assert(J3:=update_neq id_sub v (lTerm_to_term (snd a)) x1 H21).
           simp lft in J3. simp lft.
        -- assert(J:=Forall_In Reduced_Ord (map snd ps) x0). firstorder.
      * apply noop_lft. intros. apply var_of_In_tl in H14.
        -- intro. unfold Dom in H15. apply H15. assert(J:=In_lTerm_list_lTerm (V x1) x0 (map snd ps)).
           firstorder. apply disjoint_In_sym in H9 as J2. unfold disjoint_In in J2. 
           assert (J4:=ListUtil.in_appr (V x1) (snd a) (app_list_lTerm (map snd ps)) H16).
           simpl in J2. apply J2 in J4. apply ListUtil.notin_app in J4. destruct J4.
           rewrite L in H17. unfold singleton_sub. assert(v<>x1).
           intro. apply H17. rewrite H19. now left. 
           assert(J3:=update_neq id_sub v (lTerm_to_term (snd a)) x1 H19).
           simp lft in J3.
        -- assert(J:=Forall_In Reduced_Ord (map snd ps) x0). firstorder.
    + assert(L1:=solved_form_to_sub_not_in_domain ps x). firstorder. 
      unfold compose_sub. simp lft in *. rewrite H12. simp lft. 
      destruct (eq_dec_var v x). 
      * rewrite e in *. assert(L3:= update_eq id_sub x (lTerm_to_term (snd a))).
        simp lft in L3. unfold singleton_sub. rewrite L3. 
        apply noop_lft. intros. unfold Dom. apply Forall_inv in H8.
        assert(L1:=var_of_In_tl x0 (snd a) H8 H13). intro. apply H14.  
        assert(L2:=solved_form_to_sub_not_in_domain ps x0). firstorder. apply disjoint_In_sym in H9. 
        unfold disjoint_In in H9. assert(~ In (V x0) (fst a ++ app_list_lTerm (map fst ps))). simpl in H9.
        apply H9. now apply ListUtil.in_appl. apply ListUtil.notin_app in H16. destruct H16.
        apply H15 in H17. simp lft in H17. rewrite H17. simp lft.
        assert(L4:=H9 (V x0)). simpl in L4. 
        assert(L5:=ListUtil.in_appl (V x0) (snd a) (app_list_lTerm (map snd ps)) L1).
        apply L4 in L5. apply ListUtil.notin_app in L5. destruct L5. rewrite L in H18.
        assert(x<>x0). intro. apply H18. rewrite H20. now left. 
        assert(L5:=update_neq id_sub x (lTerm_to_term (snd a)) x0 H20). simp lft in L5.
      * assert(J:=update_neq id_sub v (lTerm_to_term (snd a)) x n0). unfold singleton_sub. 
        simp lft in *. rewrite J. simp id_sub. simp lft. rewrite H12. simp lft.
  - apply Forall_inv in H0. unfold single_variable_lTerm_Prop in H0. unfold single_variable_lTerm in H0.
    now rewrite L in H0.
Qed.
 
Lemma var_of_tl_In : forall (v:var)(tl:lTerm),
  Reduced_Ord tl -> var_of_tl v tl -> In (V v) tl.
Proof.
  intros. induction tl. inversion H0. simpl in *. destruct H0.
  - left. apply var_of_In_t in H0. clear IHtl. destruct a;simpl in *. destruct H0;inversion H0.
    destruct H0;auto. inversion H0. inversion H. inversion H1. inversion H4.
  - right. apply Reduced_Ord_remove in H. firstorder.
Qed.


Lemma solved_form_to_sub_in_domain_return_snd: forall(ps:problems)(v:var),
  solved_form ps -> In (V v) (app_list_lTerm (map fst ps)) ->
  (exists lt:lTerm, (solved_form_to_sub ps v) = (lTerm_to_term lt) 
  /\ return_snd [V v] ps = lt).
Proof.
  intros. assert(H1:=solved_form_to_sub_in_domain ps v H H0). destruct H1. destruct H1. 
  exists x. split. auto. clear H2. induction ps. inversion H0.
  simpl in H0. apply in_app_iff in H0. destruct H0.
  - clear IHps. assert(L:=H).
    unfold solved_form in H. destruct H. destruct H2. rewrite map_cons in *.
    apply Forall_inv in H2. unfold single_variable_lTerm_Prop in H2. unfold single_variable_lTerm in H2. simpl in H1.
    destruct (single_variable_lTerm_var (fst a)) eqn:J. apply single_variable_lTerm_var_simpl in J as J2.
    rewrite J2 in *. simpl. rewrite J2. inversion H0. inversion H4. destruct (beq_var v v) eqn:J1.
    -- unfold compose_sub in H1. apply NoDup_cons_iff in H. destruct H.
       assert(J3:=solved_form_to_sub_not_in_domain ps v). apply not_In_lTerm_Var in H.
        + apply solved_form_remove in L. firstorder. inversion H0. rewrite <- H14 in H12. firstorder.
          simp lft in H12. subst. rewrite H12 in H1. simp lft in H1. 
          assert (K:=update_eq id_sub v (lTerm_to_term (snd a))). simp lft in K. unfold singleton_sub in H1.
          rewrite K in H1. apply lTerm_to_term_f_equal in H1. auto. 
        + now apply solved_form_remove in L. 
    -- rewrite beq_var_refl in J1. inversion J1.
    -- inversion H4.
    -- inversion H2.
  - apply solved_form_remove in H as J. unfold solved_form in H. destruct H. simpl in H.
    apply NoDup_cons_iff in H. destruct H. destruct H2. simpl in H2. apply Forall_inv in H2.
    unfold single_variable_lTerm_Prop in H2. unfold single_variable_lTerm in H2. simpl in H1. 
    destruct (single_variable_lTerm_var (fst a)) eqn:J2. apply single_variable_lTerm_var_simpl in J2.
    simpl. rewrite J2. rewrite J2 in H. apply not_In_lTerm_Var in H;auto. destruct(beq_var v v0) eqn:J1.
    + apply beq_var_true_iff in J1. subst. exfalso. now apply H.
    + apply beq_var_false_iff in J1. firstorder. apply H10. rewrite <- H1. symmetry.
      unfold compose_sub. apply noop_lft. intros. unfold Dom. intro. apply H12.
      cut (v0 <> x0);intro. assert(L:=update_neq id_sub v0 (lTerm_to_term (snd a)) x0 H13). 
      simp lft in L. assert(J3:=solved_form_to_sub_in_domain ps v). firstorder. rewrite H14 in H11.
      assert(J3:=Forall_In Reduced_Ord (map snd ps) x1). firstorder.
      assert(L:=var_of_In_tl x0 x1 H16). firstorder. 
      assert(J3:=In_lTerm_list_lTerm (V x0) x1 (map snd ps)). firstorder.
      unfold disjoint_In in H9. assert(K:=H9 (V x0)). subst. apply K.
      -- simpl. apply ListUtil.in_appl. rewrite J2. now left.
      -- simpl. apply ListUtil.in_appr. auto.
    + inversion H2.
Qed.


Lemma solved_form_to_sub_in_domain_pair: forall(ps:problems)(v:var),
  solved_form ps -> In (V v) (app_list_lTerm (map fst ps)) ->
  (exists lt:lTerm, (solved_form_to_sub ps v) = (lTerm_to_term lt) 
  /\ In ([V v],lt) ps).
Proof.
  intros. assert(H1:=solved_form_to_sub_in_domain ps v H H0). destruct H1. destruct H1. clear H2.
  exists x. split. auto. 
  induction ps. inversion H0. assert(L:=H).
  apply solved_form_remove in H as J. simpl in H0. apply in_app_iff in H0. destruct H0.
  - left. clear IHps J. unfold solved_form in H. destruct H. destruct H2. rewrite map_cons in *.
    apply Forall_inv in H2. unfold single_variable_lTerm_Prop in H2. unfold single_variable_lTerm in H2.
    simpl in H1. destruct (single_variable_lTerm_var (fst a)) eqn:K. apply single_variable_lTerm_var_simpl in K.
    destruct a. simpl in *. subst. inversion H0. inversion H4. subst.
    -- apply NoDup_cons_iff in H. destruct H. apply solved_form_remove in L as L1.
       apply not_In_lTerm_Var in H;auto.
       assert(J:=solved_form_to_sub_not_in_domain ps v L1 H). unfold compose_sub in *. simp lft in *.
       rewrite J in H1. simp lft in H1. assert(J1:=update_eq id_sub v (lTerm_to_term l0)).
       unfold singleton_sub in H1. simp lft in J1. rewrite J1 in H1. apply lTerm_to_term_f_equal in H1.
       now rewrite H1.
    -- inversion H4.
    -- inversion H2.
  - simpl in H1. destruct (single_variable_lTerm_var (fst a)) eqn:J1. 
    -- apply single_variable_lTerm_var_simpl in J1. unfold compose_sub in H1. right. 
       apply IHps;auto. rewrite <- H1. symmetry. apply noop_lft. intros. unfold Dom. intro. apply H3.
       cut (v0 <> x0);intro. assert(L1:=update_neq id_sub v0 (lTerm_to_term (snd a)) x0 H4). 
       simp lft in L1. assert(J3:=solved_form_to_sub_in_domain ps v J H0). destruct J3. destruct H5.
       rewrite H5 in H2. unfold solved_form in J. destruct J. destruct H8. destruct H9.
       assert(J3:=Forall_In Reduced_Ord (map snd ps) x1 H9 H6). 
       assert(L4:=var_of_In_tl x0 x1 J3 H2). 
       assert(J4:=In_lTerm_list_lTerm (V x0) x1 (map snd ps) L4 H6). subst.
       unfold solved_form in H. destruct H. destruct H4. destruct H11. 
       unfold disjoint_In in H12. assert(K:=H12 (V x0)). apply K.
       ++ simpl. apply ListUtil.in_appl. rewrite J1. now left.
       ++ simpl. apply ListUtil.in_appr. auto.
    -- firstorder.
Qed. 


(*
Important theorem about substitution from solved form solves the problem
*)
Theorem solved_form_sub_solves:forall(ps:problems),
  solved_form ps -> solves_problems (solved_form_to_sub ps) ps.
Proof.
  intros. induction ps. 
  - simpl in *. ufps. auto.
  - simpl in *. destruct (single_variable_lTerm_var (fst a)) eqn:J.
    + apply solved_form_remove in H as J2. firstorder. ufps. apply Forall_cons.
      ++ apply single_variable_lTerm_var_simpl in J. unfold lhs. unfold rhs. simpl.
         unfold lhs. rewrite J. unfold lftl at 1. simpl. simp lft. unfold compose_sub.
         assert(J1:=solved_form_to_sub_not_in_domain ps v). apply NoDup_cons_iff in H.
         destruct H. rewrite J in H. apply not_In_lTerm_Var in H;firstorder. 
         simp lft in H9. rewrite H9. simp lft. unfold singleton_sub. 
         assert (J3:=update_eq id_sub v (lTerm_to_term (snd a))). simp lft in J3. 
         rewrite J3. unfold rhs. 
         assert(lftl
         (fun v0 : var => lft (update_sub id_sub v (lTerm_to_term (snd a)))
            (solved_form_to_sub ps v0)) (snd a) = (snd a)).
        -- apply noop_lft_tl. intros. unfold Dom. intro. apply H11.
           apply var_of_tl_In in H10.
           +++ assert(J1:=solved_form_to_sub_not_in_domain ps x). firstorder.
               assert(J2:=ListUtil.in_appl (V x) (snd a) (app_list_lTerm (map snd ps)) H10).
               apply disjoint_In_sym in H6 as J4. unfold disjoint_In in J4. apply J4 in J2.
               apply ListUtil.notin_app in J2. destruct J2. apply H12 in H14. simp lft in H14.
               rewrite H14. simp lft. rewrite J in H13. assert(v<>x). intro.
               apply H13. rewrite H15. now left. 
               assert(K:=update_neq id_sub v (lTerm_to_term (snd a)) x H15). simp lft in K.
           +++ now apply Forall_inv in H5.
        -- rewrite H10. apply lr_sym. apply lTerm_eqv_tl_singleton.
      ++ clear J H0 (*H1*) H2 H3 H H4 H5 H6. apply Forall_map. apply Forall_map in H7.
         apply Forall_forall. intros. assert(L:=Forall_In (fun x : problem =>
         lhs (apply_sub_problem (solved_form_to_sub ps) x) =l=
         rhs (apply_sub_problem (solved_form_to_sub ps) x)) ps x H7 H). simpl in L. simpl.
         repeat rewrite compose_sub_lft.
         assert(J1:=lTerm_eqv_lftl (singleton_sub v (lTerm_to_term (snd a))) _ _ L). auto.
    + firstorder. apply Forall_inv in H0. unfold single_variable_lTerm_Prop in H0. 
      unfold single_variable_lTerm in H0. rewrite J in H0. inversion H0.
Qed.


Lemma In_exists_ps:forall(p:problem)(ps:problems),
  In p ps -> (exists ps1 ps2:problems, ps = ps1 ++ p :: ps2).
Proof.
  intros. induction ps. inversion H. destruct H.
  - rewrite H. exists nil. simpl. exists ps. auto.
  - firstorder. rewrite H0. exists (a::x). exists x0.  auto.
Qed. 

Theorem solved_form_sub_mgu_helper:forall(ps:problems)(sb:sub),
  solved_form ps -> solves_problems sb ps -> leq_sub_xor (solved_form_to_sub ps) sb.
Proof.
  intros. unfold leq_sub_xor. intros. intros. firstorder.
  destruct (In_dec (V v) (app_list_lTerm (map fst ps))).
  - assert(J:=solved_form_to_sub_in_domain ps v). firstorder. unfold compose_sub.
    rewrite H4. 
    unfold solves_problems in H0. unfold equal_problems in H0. unfold equal_problem in H0.
    unfold apply_sub_problems in H0. assert(J1:=solved_form_to_sub_in_domain_pair ps v).
    firstorder. apply In_exists_ps in H7. firstorder. rewrite H7 in H0.
    rewrite map_app in H0. rewrite map_cons in H0. apply Forall_elt in H0.
    unfold lhs in H0. unfold rhs in H0. simpl in H0. simp lft in H0. rewrite H6 in H4.
    apply lTerm_to_term_f_equal in H4. subst. exists sb. apply eqv_sym.
    apply lTerm_eqv_Complete. clear H5 i H3 H2 H1 H H6. apply term_eqv_ok.
    assert(K:=lftl_lft_correct sb x). rewrite <- K. apply lTerm_eqv_Complete.
    assert([sb v] =l= term_to_lTerm (sb v)).
    + apply listTransCorrect_lr_term.
    + apply lr_trans with ([sb v]). now apply lr_sym. 
      assert (K1:=listTransCorrect_lr (lftl sb x)). apply lr_sym. apply lr_trans with (lftl sb x).
      now apply lr_sym. now apply lr_sym.
  - assert(J:=solved_form_to_sub_not_in_domain ps v). firstorder. simp lft in H4. unfold compose_sub.
    rewrite H4. exists sb. simp lft. apply eqv_ref.
Qed.


(*
Important theorem about substitution from solved form is mgu
*)
Theorem solved_form_sub_mgu:forall(ps:problems),
  solved_form ps -> mgu_xor (solved_form_to_sub ps) ps.
Proof.
  intros. unfold mgu_xor. intros. assert(J1:= solved_form_sub_mgu_helper ps sb1). firstorder.
Qed.


(* ========================================================================= *)
(*  End Solved Form   *)
(* ========================================================================= *)

 





(* ========================================================================= *)
(*  Problem Set   *)
(* ========================================================================= *)


Definition problems_set:=prod problems problems.

Definition measure(pss:problems_set):nat:=
  (length_nat (fst pss)).

Definition Rproblem(p:problem):problem:=
  (Reducing_lr_Ord (fst p), Reducing_lr_Ord (snd p)).

Definition Rproblems(ps:problems):problems:=
  map Rproblem ps.

Definition problem_to_sub(p:problem):option (var * sub).
  remember (rawP_to_reducedP p) as rp.
  destruct (a_var_in_lTerm (fst rp)) eqn:H.
  - exact (Some (v, (singleton_sub v (lTerm_to_term (remove (V v) (fst rp)))))).
  - exact None.
Defined.

Definition step(pss:problems_set):problems_set:=
  match pss with
  |([], _) => pss
  |(p::pss',sp) => match (lTerm_eqv_bool (fst p) []) with
                  | true => (pss',sp)
                  | false =>  match problem_to_sub p with
                              |Some (v,sb) => 
                                (
                                Rproblems (apply_sub_problems sb pss')
                                ,
                                ([V v], (remove (V v) (fst p))) ::
                                Rproblems (apply_sub_problems sb sp)
                                )
                              |None => pss
  end end end.

Definition fixed_pss(pss:problems_set):Prop:=
  step pss = pss.


Lemma map_same_length{X Y:Type}:forall(l:list X)(f:X -> Y),
  length_nat l = length_nat (map f l).
Proof.
  intros. induction l;simpl;auto.
Qed.

Lemma measure_not_change_apply_sub_eqns:forall(ps1 ps2:problems)(sb:sub),
  measure (ps1,ps2) = measure((apply_sub_problems sb ps1),ps2).
Proof.
  intros. unfold measure. simpl.
  unfold apply_sub_problems. assert(J:= map_same_length ps1 (apply_sub_problem sb)). auto.
Qed.

Lemma measure_not_change_rawPs_to_ReducedPs:forall(ps1 ps2:problems),
  measure (ps1,ps2) = measure((rawPs_to_reducedPs ps1),ps2).
Proof. 
  intros. unfold measure. simpl.
  unfold rawPs_to_reducedPs. now rewrite <- map_same_length.
Qed.
  
Lemma step_decrease_or_fixed:forall(pss:problems_set),
  measure (step pss) < measure pss \/ fixed_pss pss.
Proof.
  intros. destruct pss. induction p.
  - right. unfold fixed_pss. auto.
  - simpl. destruct (problem_to_sub a) eqn:J.
    + destruct p1.
      unfold apply_sub_problems. unfold measure. simpl. unfold Rproblems. 
      destruct (lTerm_eqv_bool (fst a) []). auto. simpl.
      rewrite <- map_same_length. rewrite <- map_same_length. lia.
    + destruct (lTerm_eqv_bool (fst a) []) eqn:J1. auto. right. unfold fixed_pss. simpl. 
      rewrite J. rewrite J1. auto.
Qed.
 

Fixpoint steps(measure:nat)(sys:problems_set):problems_set:=
  match measure with
  |0 => sys
  |S measure' => (steps measure' (step sys))
  end.


Lemma step_not_decrease_idpt:forall(sys:problems_set)(n:nat),
  fixed_pss sys -> steps n sys = sys.
Proof.
  intros. unfold fixed_pss in H. induction n.
  - auto.
  - simpl. rewrite H. auto.
Qed. 

Lemma list_lenght_correct{X:Type}: forall(l1 l2: list X),
  l1 = l2 -> length_nat l1 = length_nat l2.
Proof.
  intros. rewrite H. auto.
Qed.

Lemma steps_nil:forall(p:problems)(n:nat),
  steps n ([],p) = ([],p).
Proof.
  induction n;auto.
Qed.

Lemma steps_0:forall(sys:problems_set),
  steps 0 sys = sys.
Proof.
  auto.
Qed.

Lemma steps_step_plus1_right:forall(sys:problems_set)(n:nat),
  steps n (step sys) = (steps (S n) sys).
Proof.
  intros. simpl. auto.
Qed.

Lemma steps_step_plus1_left:forall(sys:problems_set)(n:nat),
  step (steps n sys) = (steps (S n) sys).
Proof.
  intros sys n. generalize dependent sys.
  induction n;simpl;intros. auto.
  rewrite IHn. repeat rewrite steps_step_plus1_in. auto.
Qed.

Lemma steps_step_assoc:forall(sys:problems_set)(n:nat),
  steps n (step sys) = step (steps n sys).
Proof.
  intros. rewrite steps_step_plus1_right. rewrite steps_step_plus1_left. auto.
Qed.


Lemma steps_plus_1_fixed:forall(sys:problems_set)(n:nat),
  fixed_pss (steps n sys) -> fixed_pss (steps (S n) sys).
Proof.
  intros. rewrite <- steps_step_plus1_right. unfold fixed_pss in *.
  rewrite steps_step_plus1_left in H. rewrite steps_step_plus1_left.
  rewrite steps_step_assoc. rewrite H. rewrite steps_step_assoc. auto.
Qed.

Lemma steps_decrease_or_fixed:forall (sys:problems_set)(n:nat),
  fixed_pss (steps n sys) \/ measure (steps n sys) > measure (steps (S n) sys).
Proof.
  intros. assert(H:=step_decrease_or_fixed (steps n sys)). destruct H.
  - right. rewrite steps_step_plus1_left in H. lia.
  - now left.
Qed.

Lemma steps_decrease_or_fixed_strong:forall (sys:problems_set)(n:nat),
  fixed_pss (steps n sys) \/ measure sys >= n + measure (steps n sys).
Proof.
  induction n;simpl.
  - right. lia.
  - destruct IHn.
    + left. rewrite steps_step_assoc. unfold fixed_pss in *. congruence.
    + assert(J:=steps_decrease_or_fixed sys n). destruct J.
      -- left. unfold fixed_pss in *. repeat rewrite steps_step_assoc. congruence.
      -- right. simpl in *. lia.
Qed.

Lemma steps_fixed_sys:forall(sys:problems_set),
  fixed_pss(steps (measure sys) sys).
Proof.
  intros. assert (J:=steps_decrease_or_fixed_strong sys (measure sys)).
  assert(J1:=steps_decrease_or_fixed sys (measure sys)).
  destruct J;destruct J1; auto;lia. 
Qed.


Lemma step_idpt:forall(sys:problems_set),
  fixed_pss sys -> step sys = sys.
Proof.
  auto.
Qed.

Lemma steps_idpt:forall(sys:problems_set),
  fixed_pss sys -> forall n:nat, steps n sys = sys.
Proof.
  intros. induction n. auto. simpl. rewrite steps_step_assoc. rewrite IHn. auto.
Qed.

Lemma step_invariant(p:problems_set -> Prop) (sys:problems_set)(n:nat):
  p sys -> (forall sys, p sys -> p (step sys)) -> p (steps n sys).
Proof.
  intros. induction n. auto.
  simpl. rewrite steps_step_assoc. apply H0. auto.
Qed.


Definition problems_set_ready(ps:problems):problems_set:=
  ((rawPs_to_reducedPs ps),[]).


Lemma map_fst_comm_map_problems:forall(P Q: lTerm -> lTerm)(ps:problems),
  map fst (map (fun p : problem => (P (fst p), Q (snd p))) ps) = 
  map P (map fst ps).
Proof.
intros. induction ps;simpl. auto. now f_equal.
Qed.

Lemma map_snd_comm_map_problems:forall(P Q: lTerm -> lTerm)(ps:problems),
  map snd (map (fun p : problem => (P (fst p), Q (snd p))) ps) = 
  map Q (map snd ps).
Proof.
intros. induction ps;simpl. auto. now f_equal.
Qed.















(* ======================== Solved Form ============================*)

Definition Reduced_Ord_problem(p:problem):Prop:=
  Reduced_Ord (fst p) /\ Reduced_Ord (snd p).


Lemma sort_not_same_length_false:forall(tl1 tl2:lTerm),
  AReduced tl1 -> AReduced tl2 ->
  length_nat tl1 <> length_nat tl2 -> sort_term tl1 = sort_term tl2 -> False.
Proof.
  intros. apply sort_ltSorted_Permutation in H. apply sort_ltSorted_Permutation in H0.
  apply Permutation_length in H. apply Permutation_length in H0.
  congruence.
Qed.


Lemma rawP_to_reducedP_Reduced:forall(p:problem),
  Reduced_Ord (fst (rawP_to_reducedP p)).
Proof.
  intros. unfold rawP_to_reducedP. simpl. apply Reducing_lr_Ord_Correct_Reduced_Ord.
Qed.

Lemma count_occ_remove:forall(lt:lTerm)(t:term),
  count_occ term_beq_syn_dec lt t = 0 \/ count_occ term_beq_syn_dec lt t = 1
  -> count_occ term_beq_syn_dec (remove t lt) t = 0.
Proof.
  intros. destruct H.
  - apply (count_occ_not_In term_beq_syn_dec) in H as H1.
    apply remove_noop in H1. now rewrite H1.
  - apply count_remove in H. auto.
Qed.

Lemma Not_In_Reduced_lTerm:forall(lt:lTerm)(v:var),
  ~ In (V v) (remove (V v) (Reducing_lr lt)).
Proof.
  intros. apply (count_occ_not_In term_beq_syn_dec).
  unfold Reducing_lr. assert(AReduced (AReducing_lr lt)). apply AReducing_lr_Correct_Reduced.
  remember (AReducing_lr lt) as al. 
  apply count_occ_remove. apply UReducing_NReducing_homo in H.
  rewrite H. unfold NReducing. rewrite count_occ_rev_eq.
  assert(V v <> T0). intro. inversion H0. apply (count_occ_NUReducing _ al) in H0.
  rewrite <- H0. 
  assert(J:=count_NReducing'_1_0 al (V v)). 
  destruct (Even_Odd_dec (count_occ term_beq_syn_dec al (V v))) eqn:J1.
  now left. now right.
Qed.

Lemma Permutation_remove_sort_term:forall(lt1 lt2:lTerm)(t:term)(v:var),
  Permutation lt1 lt2 -> ~ In (V v) (remove t lt1) -> ~ In (V v) (remove t lt2).
Proof.
  intros. induction H. 
  - auto.
  - simpl in *. destruct (term_beq_syn x t);firstorder.
    apply (Permutation_Not_In _ _ (V v)) in H;auto.
  - simpl in *. destruct (term_beq_syn y t) eqn:Hyt;destruct(term_beq_syn x t)eqn:Hxt.
    + apply term_beq_syn_true_iff in Hyt. apply term_beq_syn_true_iff in Hxt. subst. auto.
    + auto.
    + auto.
    + intro. apply H0. simpl in H. destruct H. simpl. right. now left. destruct H.
      simpl. now left. right. now right.
  - firstorder.
Qed.
    

Lemma Not_In_Reduced_Ord_lTerm:forall(lt:lTerm)(v:var),
  ~ In (V v) (remove (V v) (Reducing_lr_Ord lt)).
Proof.
  intros. unfold Reducing_lr_Ord. assert(Reduced (Reducing_lr lt)).
  apply Reducing_lr_Correct_Reduced. inversion H.
  assert(L:=sort_ltSorted_Permutation _ H0).
  assert(L1:=Permutation_remove_sort_term _ _ (V v) v L). apply L1.
  apply Not_In_Reduced_lTerm.
Qed.


Lemma In_remove:forall(t1 t2:term)(lt:lTerm),
  In t1 (remove t2 lt) -> In t1 lt.
Proof.
  intros. induction lt. inversion H. simpl in *. destruct (term_beq_syn a t2)eqn:J.
  now right. simpl in H. destruct H. now left. firstorder.
Qed.

Lemma remove_ltSorted:forall(t:term)(l:list term),
  ltSorted l -> ltSorted (remove t l).
Proof.
  intros. induction l;simpl;try constructor.
  destruct (term_beq_syn a t) eqn:J. 
  apply ltSorted_remove in H;firstorder.
  apply ltSorted_remove in H as H1. firstorder.
  apply ltSorted_cons_forall_Rvc_smallest. auto. intros.
  apply (ltSorted_forall_Rvc_smallest _ l). auto.
  now apply In_remove in H2.
Qed.

Lemma remove_NReduced_Ord:forall(t:term)(lt:lTerm),
  Reduced_Ord lt -> Reduced_Ord (remove t lt).
Proof.
  intros. inversion H;subst. inversion H0;subst. constructor;try constructor.
  - induction lt. constructor. simpl. apply Reduced_Ord_remove in H. inversion H.
    inversion H5. destruct (term_beq_syn a t);auto;firstorder. 
    destruct a;try constructor;auto. inversion H2.
  - induction lt. constructor. simpl. apply Reduced_Ord_remove in H. inversion H.
    inversion H5. destruct (term_beq_syn a t);auto;firstorder. 
    inversion H3;subst;constructor;auto; now apply (not_In_remove _ t) in H15.
  - induction lt. constructor. simpl. apply Reduced_Ord_remove in H. inversion H.
    inversion H5. destruct (term_beq_syn a t);auto;firstorder. inversion H4;constructor;auto.
  - apply remove_ltSorted. auto.
Qed.

Lemma var_of_neq:forall(v1 v2:var)(t:term),
  var_of v1 t -> ~ var_of v2 t -> v1 <> v2.
Proof.
  intros. destruct (eq_dec_var v1 v2).
  rewrite e in *. now apply H0 in H. auto.
Qed.

Lemma problem_to_sub_not_var_of:forall(p:problem)(sb:sub)(v:var),
  problem_to_sub p = Some (v,sb) -> ~ var_of v (sb v).
Proof.
  intros. unfold problem_to_sub in H.  
  destruct (a_var_in_lTerm (fst (rawP_to_reducedP p))) eqn: J.
  - inversion H;subst. clear H. unfold rawP_to_reducedP in J. simpl in J.
    remember ((Reducing_lr_Ord (lhs p ++ rhs p))) as lt. apply a_var_in_lTerm_In in J.
    assert(J1:=Not_In_Reduced_lTerm lt v). assert(Reduced_Ord(lt)).
    rewrite Heqlt. apply Reducing_lr_Ord_Correct_Reduced_Ord.
    inversion H. apply Reduced_Reducing in H0. rewrite H0 in J1.
    apply (remove_NReduced_Ord (V v)) in H.
    assert (J2:= Not_In_tl_var_of v _ H J1). remember ((lTerm_to_term (remove (V v) lt))).
    unfold singleton_sub.  
    assert(J3:=update_eq id_sub v t). simp lft in J3. rewrite J3. auto.
  - inversion H.
Qed.

Lemma problem_to_sub_not_In:forall(p:problem)(sb:sub)(v:var),
  problem_to_sub p = Some (v,sb) -> lft sb (sb v) = sb v.
Proof.
  intros. unfold problem_to_sub in H.  
  destruct (a_var_in_lTerm (fst (rawP_to_reducedP p))) eqn: J.
  - inversion H;subst. clear H. unfold rawP_to_reducedP in J. simpl in J.
    remember ((Reducing_lr_Ord (lhs p ++ rhs p))) as lt. apply a_var_in_lTerm_In in J.
    assert(J1:=Not_In_Reduced_lTerm lt v). assert(Reduced_Ord(lt)).
    rewrite Heqlt. apply Reducing_lr_Ord_Correct_Reduced_Ord.
    inversion H. apply Reduced_Reducing in H0. rewrite H0 in J1.
    apply (remove_NReduced_Ord (V v)) in H.
    assert (J2:= Not_In_tl_var_of v _ H J1). remember ((lTerm_to_term (remove (V v) lt))).
    unfold singleton_sub at 2 3.  
    assert(J3:=update_eq id_sub v t). simp lft in J3. rewrite J3. apply noop_lft.
    intros. unfold Dom. intro. apply H4. assert(J4:=var_of_neq _ _ _ H3 J2).
    unfold singleton_sub. assert(v<>x). intro. now apply J4.
    assert(K:=update_neq id_sub v t x H5). simp lft in K.
  - inversion H.
Qed.

Lemma In_UReducing:forall(t:term)(lt:lTerm),
  t <> T0 ->
  In t lt -> In t (UReducing lt).
Proof.
  intros. induction lt. inversion H0.
  simpl in H0. destruct H0.
  simpl. destruct (term_beq_syn a T0) eqn:J. apply term_beq_syn_true_iff in J.
  congruence. simpl. now left. simpl. destruct (term_beq_syn a T0) eqn:J.
  firstorder. firstorder.
Qed.

Lemma not_n_add_in:
  forall (t1 t2 : term) (tl : lTerm),
  t1 <> t2 -> ~ In t1 (n_add t2 tl) -> ~ In t1 tl .
Proof.
  intros. induction tl. auto. simpl in *.
  destruct (term_beq_syn a t2) eqn:J.
  - apply term_beq_syn_true_iff in J. subst. intro. destruct H1. now apply H.
    assert(L:=not_in_n_add t1 t2 _ H H0). firstorder.
  - apply not_in_cons in H0. destruct H0. firstorder.
Qed.

Lemma n_add_in:forall(t1 t2:term)(tl:lTerm),
  t1 <> t2 -> In t1 (n_add t2 tl) -> In t1 tl.
Proof.
  intros. induction tl. simpl in H0. destruct H0. symmetry in H0. now apply H in H0.
  inversion H0. simpl in *.
  destruct (term_beq_syn a t2)eqn:J.
  - apply term_beq_syn_true_iff in J. rewrite J in *. right. apply IHtl.
    destruct (In_dec t2 tl).
    + apply n_add_In in i. rewrite i. assert(L1:=neq_In_remove t1 t2 tl H). apply L1. auto.
    + apply n_add_not_In in n. rewrite n. apply ListUtil.in_appl. auto.
  - simpl in *. destruct H0. apply term_beq_syn_false_iff in J. firstorder.
    firstorder.
Qed.

Lemma NReducing'_notIn_list:forall(tl1 tl2:lTerm)(v:var),
  ~ In (V v) tl1 -> 
  In (V v) (NReducing' (tl1 ++ tl2)) ->
  In (V v) (NReducing' tl2).
Proof.
  intros. induction tl1;simpl in *. assert(J:=NReducing'_notIn_preserve (V v) tl2).
  destruct (In_dec (V v) tl2). auto. firstorder.

  destruct (term_beq_syn_dec (V v) a).
  - rewrite e in H. exfalso. apply H. now left.
  - assert (L:=n_add_in _ _ (NReducing' (tl1++tl2)) n H0). 
    firstorder.
Qed.

Lemma Not_var_of_In_t:
  forall (v : var) (t : term), ~ var_of v t -> ~ In (V v) (term_to_lTerm t).
Proof.
  intros. intro. apply H. clear H. 
  induction t;simpl in *. inversion H0;inversion H.
  destruct H0. destruct (eq_dec_var v v0)eqn:L. auto. inversion H. now apply n.
  inversion H. apply in_app_iff in H0;firstorder.
Qed.


Lemma Not_In_lftl_sub:forall(tl:lTerm)(v:var)(t:term),
  ~ var_of v t -> 
  ~ In (V v) (Reducing_lr (lftl (singleton_sub v t) tl)).
Proof.
  intros. induction tl.
  - auto.
  - simpl. unfold Reducing_lr. apply not_In_URducing. unfold NReducing.
    intro. apply IHtl. apply in_rev in H0.
    unfold Reducing_lr. assert(V v <> T0). intro. inversion H1.
    apply (In_UReducing _ (NReducing (AReducing_lr (lftl (singleton_sub v t) tl)))) in H1. auto.
    unfold NReducing. apply -> in_rev. 
    assert(lft (singleton_sub v t) a :: lftl (singleton_sub v t) tl = [lft (singleton_sub v t) a] ++ lftl (singleton_sub v t) tl).
    auto. rewrite H2 in H0. rewrite <- AReducing_lr_app in H0.
    remember (AReducing_lr (lftl (singleton_sub v t) tl)) as atl.
    assert(J1:=NReducing'_notIn_list (AReducing_lr [lft (singleton_sub v t) a]) atl v).
    apply J1;auto. simpl. destruct (Oplus_term (lft (singleton_sub v t) a)) eqn:J.
    + rewrite app_nil_r. assert(L:=Not_var_of_In_t v (lft (singleton_sub v t) a)).
      apply L. clear L IHtl atl Heqatl H0 H1 H2 J1 J. induction a;simp lft;simpl.
      -- auto.
      -- destruct (eq_dec_var v v0). rewrite e in *. assert(L:=update_eq id_sub v0 t).
         simp lft in L. unfold singleton_sub. rewrite L. auto.
         assert(L:=update_neq id_sub v t v0 n). simp lft in L. unfold singleton_sub.
         rewrite L. simp id_sub. simpl. destruct (eq_dec_var v v0). exfalso.
         now apply n. auto.
      -- intro. destruct H0. now apply IHa1. now apply IHa2.
    + destruct a;simp lft;auto;simpl;intro;destruct H3;try inversion H3.
      destruct (eq_dec_var v v0).
      -- rewrite e in H3. assert(L:=update_eq id_sub v0 t). simp lft in L.
         unfold singleton_sub in H3. rewrite L in H3. rewrite H3 in *. apply H. simpl.
         destruct(eq_dec_var v v0). auto. now apply n.
      -- assert(L:=update_neq id_sub v t v0 n). simp lft in L. unfold singleton_sub in H3.
         rewrite L in H3. simp id_sub in H3. inversion H3. now apply n.
Qed.


Lemma incl_not_In:forall(tl1 tl2:lTerm)(t:term),
  incl tl1 tl2 -> ~ In t tl2 -> ~ In t tl1.
Proof.
  intros. intro. apply H0. auto.
Qed.

Lemma Not_In_app_list_lTerm:forall(llt:list lTerm)(t:term),
  ~ In t (app_list_lTerm llt) <-> Forall (fun lt=> ~ In t lt) llt.
Proof.
  split; intros.
  - induction llt. auto. simpl in H. apply ListUtil.notin_app in H.
    destruct H. firstorder.
  - induction llt. auto. simpl. apply ListUtil.notin_app. split.
    now apply Forall_inv in H. apply Forall_inv_tail in H. firstorder.
Qed.


Lemma app_list_lTerm_nil:forall (llt:list lTerm),
  app_list_lTerm llt = [] <-> Forall (fun l=> l = []) llt.
Proof.
  split;intros. induction llt.
  - auto.
  - simpl in H. apply app_eq_nil in H. destruct H.
    apply Forall_cons. auto. firstorder.
  - induction llt. auto. simpl. apply Forall_inv in H as J. rewrite J. simpl. 
    apply Forall_inv_tail in H. firstorder. 
Qed.

Lemma steps_simpl_nil_sndps1:forall(sys:problems_set),
  app_list_lTerm (map snd (fst sys)) = [] -> app_list_lTerm (map snd (fst (step sys))) = [].
Proof.
  intros. unfold step. destruct sys. destruct p.
  + simpl in *. auto.
  + destruct (lTerm_eqv_bool (fst p) []) eqn:JJ.
    * simpl in *. apply list_lenght_correct in H. simpl in H. rewrite length_nat_app in H.
      simpl in H. destruct (length_nat (snd p)). simpl in H. apply length_nat_0 in H. auto. lia.
    *
    destruct (problem_to_sub p) eqn:J.
    -- unfold problem_to_sub  in J. destruct (a_var_in_lTerm (fst (rawP_to_reducedP p))) eqn:J1.
       ++ inversion J. simpl. unfold Rproblems. unfold Rproblem. unfold apply_sub_problems.
          unfold apply_sub_problem. rewrite map_snd_comm_map_problems. rewrite map_snd_comm_map_problems.
          simpl in *. remember (lTerm_to_term
          (remove (V v) (Reducing_lr_Ord (lhs p ++ rhs p)))) as t.
          clear J1 Heqt J H1. 
          apply app_eq_nil in H. destruct H. remember (map snd p1) as ll.
          clear Heqll.
          induction ll. auto. simpl in H0. apply app_eq_nil in H0. destruct H0.
          simpl. rewrite H0. simpl. firstorder.
        ++ inversion J.
    -- auto.
Qed.


Lemma steps_disjoint_snd_ps1_nil:forall(ps:problems)(ps1 ps2:problems),
  steps (measure (problems_set_ready ps)) (problems_set_ready ps) = (ps1,ps2) ->
  app_list_lTerm (map snd ps1) = [].
Proof.
  intros. assert(L:=step_invariant 
  (fun p=> (app_list_lTerm(map snd (fst p)))=[])
  (problems_set_ready ps) (measure (problems_set_ready ps))).
  rewrite H in L. simpl in L. apply L.
  - clear L H. unfold rawPs_to_reducedPs. unfold rawP_to_reducedP. induction ps. auto. 
    simpl. auto.
  - intros. apply steps_simpl_nil_sndps1. auto.
Qed.


Ltac umap_fst_comm:= unfold Rproblems in *; unfold Rproblem in *;
     unfold apply_sub_problems in *; unfold apply_sub_problem in *;
     rewrite map_fst_comm_map_problems in *; rewrite map_fst_comm_map_problems in *.

Ltac umap_snd_comm:= unfold Rproblems in *; unfold Rproblem in *;
     unfold apply_sub_problems in *; unfold apply_sub_problem in *;
     rewrite map_snd_comm_map_problems in *; rewrite map_snd_comm_map_problems in *.



Lemma In_app_list_lTerm_problem:forall (v:var)(ps:problems)(s:sub),
In (V v) (app_list_lTerm (map Reducing_lr_Ord (map (lftl s) (map fst ps))))
-> (exists p:problem, In (V v) (Reducing_lr_Ord (lftl s (fst p)))).
Proof.
  intros. induction ps; simpl in *. inversion H.
  apply in_app_iff in H. destruct H.
  - clear IHps. exists a. auto.
  - firstorder.
Qed.

Lemma In_app_list_lTerm_problem_term:forall (t:term)(ps:problems)(s:sub),
In t (app_list_lTerm (map Reducing_lr_Ord (map (lftl s) (map fst ps))))
-> (exists p:problem, In t (Reducing_lr_Ord (lftl s (fst p)))).
Proof.
  intros. induction ps; simpl in *. inversion H.
  apply in_app_iff in H. destruct H.
  - clear IHps. exists a. auto.
  - firstorder.
Qed.

Lemma singleton_sub_eq_simple:forall(v:var)(t:term),
  singleton_sub v t v = t.
Proof.
  intros. assert (J:=update_eq id_sub v t). simp lft in J.
Qed.

Lemma singleton_sub_neq_simple:forall(v v1:var)(t:term),
  v <> v1 -> 
  singleton_sub v t v1 = (V v1).
Proof.
  intros. assert (J:=update_neq id_sub v t v1). simp lft in J. 
Qed.

Lemma In_Reducing_lr_Ord:forall(tl:lTerm)(t:term),
  In t (Reducing_lr tl) <-> In t (Reducing_lr_Ord tl).
Proof.
  split;intros.
  - unfold Reducing_lr_Ord. assert(Reduced ((Reducing_lr tl))).
    apply Reducing_lr_Correct_Reduced. inversion H0. apply sort_ltSorted_Permutation in H1.
    assert(L:=Permutation_In _ _ _ H1 H). auto.
  - unfold Reducing_lr_Ord in H. assert(Reduced ((Reducing_lr tl))).
    apply Reducing_lr_Correct_Reduced. inversion H0. apply sort_ltSorted_Permutation in H1.
    symmetry in H1.
    assert(L:=Permutation_In _ _ _ H1 H). auto.
Qed.

Lemma Not_In_Reducing_lr_Ord:forall(tl:lTerm)(t:term),
  ~ In t (Reducing_lr tl) <-> ~ In t (Reducing_lr_Ord tl).
Proof.
  split;intros.
  - unfold Reducing_lr_Ord. assert(Reduced ((Reducing_lr tl))).
    apply Reducing_lr_Correct_Reduced. inversion H0. apply sort_ltSorted_Permutation in H1.
    assert(L:=Permutation_Not_In _ _ _ H1 H). auto.
  - unfold Reducing_lr_Ord in H. assert(Reduced ((Reducing_lr tl))).
    apply Reducing_lr_Correct_Reduced. inversion H0. apply sort_ltSorted_Permutation in H1.
    symmetry in H1.
    assert(L:=Permutation_Not_In _ _ _ H1 H). auto.
Qed.

Lemma var_of_dec:forall(v:var)(t:term),
  {var_of v t} + {~var_of v t}.
Proof.
  intros. induction t.
  - now right.
  - simpl. destruct (eq_dec_var v v0);auto. 
  - destruct IHt1;destruct IHt2;simpl;auto. right. intro. destruct H; firstorder.
Qed.

Lemma Not_In_app_list_lTerm_forall:
  forall (llt : list lTerm) (t : term),
  ~ In t (app_list_lTerm llt) <-> (forall lt:lTerm, In lt llt -> ~ In t lt).
Proof.
  split;intros.
  - induction llt. inversion H0. simpl in H0. destruct H0. simpl in H. apply ListUtil.notin_app in H.
    destruct H. rewrite <- H0. auto. simpl in H. apply ListUtil.notin_app in H.
    destruct H. firstorder.
  - apply Not_In_app_list_lTerm. apply Forall_forall. auto.
Qed.


Lemma steps_Reduced_In:forall(ps:problems)(ps1 ps2:problems),
  steps (measure (problems_set_ready ps)) (problems_set_ready ps) = (ps1,ps2) ->
  Forall Reduced_Ord (map fst ps1).
Proof.
  intros. assert(L:=step_invariant 
  (fun p => Forall Reduced_Ord (map fst (fst p)))
  (problems_set_ready ps) (measure (problems_set_ready ps))).
  rewrite H in L. simpl in L. apply L.
  - unfold rawPs_to_reducedPs. unfold rawP_to_reducedP. clear H L.
    induction ps;simpl. auto. apply Forall_cons. apply Reducing_lr_Ord_Correct_Reduced_Ord.
    auto.
  - intros. clear H L. unfold step. destruct sys. destruct p. 
    + simpl. auto.
    + destruct (problem_to_sub p) eqn:J.
      -- destruct (lTerm_eqv_bool (fst p) []) eqn:JJ.
         * simpl in *. now apply Forall_inv_tail in H0.
         * 
         destruct p2. simpl. umap_fst_comm. clear H0 J.
         remember (map (lftl s) (map fst p1)) as l. clear Heql. induction l;simpl.
         auto. apply Forall_cons. apply Reducing_lr_Ord_Correct_Reduced_Ord.  
         auto.
      -- destruct (lTerm_eqv_bool (fst p) []) eqn:JJ;simpl in *; auto. now apply Forall_inv_tail in H0.
Qed.


Lemma steps_Reduced_In_anytime:forall(ps:problems)(ps1 ps2:problems)(n:nat),
  steps n (problems_set_ready ps) = (ps1,ps2) ->
  Forall Reduced_Ord (map fst ps1).
Proof.
  intros. assert(L:=step_invariant 
  (fun p => Forall Reduced_Ord (map fst (fst p)))
  (problems_set_ready ps) n).
  rewrite H in L. simpl in L. apply L.
  - unfold rawPs_to_reducedPs. unfold rawP_to_reducedP. clear H L.
    induction ps;simpl. auto. apply Forall_cons. apply Reducing_lr_Ord_Correct_Reduced_Ord.
    auto.
  - intros. clear H L. unfold step. destruct sys. destruct p. 
    + simpl. auto.
    + destruct (lTerm_eqv_bool (fst p) []) eqn:JJ;simpl in *. now apply Forall_inv_tail in H0.
      destruct (problem_to_sub p) eqn:J.
      -- destruct p2. simpl. umap_fst_comm. clear H0 J.
         remember (map (lftl s) (map fst p1)) as l. clear Heql. induction l;simpl.
         auto. apply Forall_cons. apply Reducing_lr_Ord_Correct_Reduced_Ord.  
         auto.
      -- auto.
Qed.


Lemma steps_simpl_Reduced_fstp1:forall (sys:problems_set),
  Forall Reduced_Ord (map fst (fst sys)) -> Forall Reduced_Ord (map fst (fst (step sys))).
Proof.
  intros. unfold step. destruct sys. destruct p. 
  + simpl. auto.
  + destruct (lTerm_eqv_bool (fst p) []) eqn:JJ;simpl in *. now apply Forall_inv_tail in H.
    destruct (problem_to_sub p) eqn:J.
    -- destruct p2. simpl. umap_fst_comm. clear H J.
       remember (map (lftl s) (map fst p1)) as l. clear Heql. induction l;simpl.
       auto. apply Forall_cons. apply Reducing_lr_Ord_Correct_Reduced_Ord.  
       auto.
    -- auto.
Qed.


Lemma steps_simpl_Reduced_fstp1_sndp2:forall (sys:problems_set),
  Forall Reduced_Ord (map fst (fst sys)) /\ Forall Reduced_Ord (map snd (snd sys))
  -> 
  Forall Reduced_Ord (map fst (fst (step sys))) /\ Forall Reduced_Ord (map snd (snd (step sys))).
Proof.
  intros. destruct H. split.
  ++ apply steps_simpl_Reduced_fstp1. auto.
  ++ unfold step. destruct sys. destruct p. 
    + simpl. auto.
    + destruct (lTerm_eqv_bool (fst p) []) eqn:JJ;simpl in *. auto.
      destruct (problem_to_sub p) eqn:J.
      -- destruct p2. simpl. apply Forall_cons.
         --- simpl in H. apply Forall_inv in H. assert(J1:=remove_NReduced_Ord (V v) _ H). auto.
         --- umap_snd_comm. remember (map (lftl s) (map snd p0)) as l. clear H0 H J Heql. induction l.
             simpl. auto. simpl. apply Forall_cons;auto. apply Reducing_lr_Ord_Correct_Reduced_Ord.
      -- auto.
Qed.

Lemma steps_Reduced_Out:forall(ps:problems)(ps1 ps2:problems)(n:nat),
  steps n (problems_set_ready ps) = (ps1,ps2) ->
  Forall Reduced_Ord (map snd ps2) /\ Forall Reduced_Ord (map fst ps1).
Proof.
  intros. assert(L:=step_invariant 
  (fun p => Forall Reduced_Ord (map snd (snd p)) /\ Forall Reduced_Ord (map fst (fst p)))
  (problems_set_ready ps) n). apply steps_Reduced_In_anytime in H as H0. 
  rewrite H in L. simpl in L. apply L.
  - split;auto. unfold rawPs_to_reducedPs. unfold rawP_to_reducedP. clear H L.
    induction ps;simpl. auto. apply Forall_cons. apply Reducing_lr_Ord_Correct_Reduced_Ord.
    auto.
  - intros. destruct H1. clear L H H0. assert(L:=steps_simpl_Reduced_fstp1_sndp2 sys).
    destruct L;now split.
Qed.

 
 
Lemma steps_simpl_Reduced_fstp2:forall (sys:problems_set),
  Forall Reduced_Ord (map fst (snd sys)) -> Forall Reduced_Ord (map fst (snd (step sys))).
Proof.
  intros. unfold step. destruct sys. destruct p.
  - auto.
  - destruct (lTerm_eqv_bool (fst p) []) eqn:JJ;simpl in *. auto.
    simpl in *. destruct (problem_to_sub p) eqn:J.
    + destruct p2. simpl. apply Forall_cons. 
      -- repeat constructor. auto.
      -- clear J. umap_fst_comm. remember ((map (lftl s) (map fst p0))) as llt. clear Heqllt.
         induction llt;simpl. auto. apply Forall_cons. apply Reducing_lr_Ord_Correct_Reduced_Ord.
         auto.
    + auto.
Qed.

Lemma steps_Reduced_Var:forall(ps:problems)(ps1 ps2:problems)(n:nat),
  steps n (problems_set_ready ps) = (ps1,ps2) ->
  Forall Reduced_Ord (map fst ps2).
Proof.
  intros. assert(L:=step_invariant 
  (fun p => Forall Reduced_Ord (map fst (snd p)))
  (problems_set_ready ps) n). apply steps_Reduced_In_anytime in H as H0. 
  rewrite H in L. simpl in L. apply L.
  - auto.
  - intros. clear H L. apply steps_simpl_Reduced_fstp2. auto.
Qed.
  

Lemma In_app_list_lTerm_Ran_In:forall(v:var)(t:term)(llt:list lTerm),
  In (V v) (app_list_lTerm llt) -> In t (app_list_lTerm (map (lftl (singleton_sub v t)) llt)).
Proof.
  intros. induction llt. inversion H.
  simpl in H. apply in_app_iff in H. destruct H.
  - simpl. cut (In t (lftl (singleton_sub v t) a)). intro.
    apply(ListUtil.in_appl t _ _ H0). clear IHllt. induction a.
    + inversion H.
    + simpl in H. destruct H;simpl. left. rewrite H. simp lft. apply singleton_sub_eq_simple.
      firstorder.
  - simpl. assert(J:=ListUtil.in_appr t (lftl (singleton_sub v t) a) 
    (app_list_lTerm (map (lftl (singleton_sub v t)) llt))). firstorder.
Qed.


Lemma lftl_noop:forall(v:var)(t:term)(lt:lTerm),
  Reduced_Ord lt ->
  ~ In (V v) lt ->
  lftl (singleton_sub v t) lt = lt.
Proof.
  intros. induction lt. auto. simpl in *. apply Decidable.not_or in H0.
  destruct H0. f_equal. inversion H;subst. inversion H2;subst.
  destruct a;simp lft;auto.
  apply singleton_sub_neq_simple. intro. rewrite H7 in *. now apply H0.
  inversion H4. apply Reduced_Ord_remove in H. firstorder.
Qed.

Lemma map_lftl_noop:forall(v:var)(t:term)(llt:list lTerm),
  Forall Reduced_Ord llt ->
  ~ In (V v) (app_list_lTerm llt) ->
  map (lftl (singleton_sub v t)) llt = llt.
Proof.
  intros. induction llt.
  - auto.
  - simpl in *. apply ListUtil.notin_app in H0. destruct H0.
    f_equal.
    + apply Forall_inv in H. apply (singleton_sub_not_dom);auto.
    + apply Forall_inv_tail in H. firstorder. 
Qed.



Lemma Reduced_Ord_Reducing_lr_Ord_app_list_lTerm:forall(llt:list lTerm),
  Forall Reduced_Ord llt -> 
  (map Reducing_lr_Ord llt) = llt.
Proof.
  intros. induction llt. auto. simpl. f_equal. apply Forall_inv in H. 
  now apply Reduced_Ord_Reducing_lr_Ord in H.
  apply Forall_inv_tail in H. firstorder.
Qed.




Lemma not_In_Var_lTerm_general: forall (v : var) (llt : list lTerm),
  ~ In (V v) (app_list_lTerm llt) -> ~ In [V v] llt.
Proof. 
  intros. induction llt. auto.
  simpl in *. apply ListUtil.notin_app in H. destruct H.
  intro. destruct H1. rewrite H1 in H. apply H. now left. firstorder.
Qed.

Lemma var_of_tl_to_var_of:forall(v:var)(lt:lTerm),
  var_of_tl v lt -> var_of v (lTerm_to_term lt).
Proof.
  intros. induction lt. inversion H.
  simpl in *. destruct H. now left. firstorder.
Qed.

Lemma lftl_In_Ran_Not_In:forall(v v1:var)(t:term)(lt:lTerm),
  Reduced_Ord lt ->
  ~ In (V v) lt -> ~ var_of v t -> v <> v1 ->
  ~ In (V v) (lftl (singleton_sub v1 t) lt).
Proof.
  intros. destruct (In_dec (V v1) lt).
  - induction lt. auto. simpl in *. apply Classical_Prop.and_not_or.
    split.
    + intro. destruct i. 
      -- rewrite H4 in *. simp lft in H3. rewrite singleton_sub_eq_simple in H3. rewrite H3 in *.
         apply H1. simpl. destruct (eq_dec_var v v). auto. now apply n.
      -- apply H0. destruct(In_dec (V v) lt). now right. 
         destruct a; simp lft in H3;try inversion H3.
         destruct (eq_dec_var v1 v0). rewrite e in *. 
         rewrite singleton_sub_eq_simple in H3. rewrite H3 in *. exfalso.  
         apply H1. simpl. destruct (eq_dec_var v v). auto. now apply n.
         assert(L:=singleton_sub_neq_simple v1 v0 t n0). rewrite L in H6. inversion H6.
         rewrite H7 in *. firstorder.
    + apply Decidable.not_or in H0. destruct H0. destruct i.
      -- inversion H;subst. inversion H5;subst.
         destruct(In_dec (V v1) lt). 
         ++ apply IHlt;auto. apply Reduced_Ord_remove in H. auto.
         ++ rewrite noop_lft_tl;auto. intros. unfold Dom. intro.
            apply H10. apply var_of_tl_to_var_of in H9. apply Reduced_Ord_remove in H.
            assert(L:=var_of_In_tl x lt H H9). destruct (eq_dec_var v1 x).
            --- rewrite e in *. now apply n in L.
            --- apply singleton_sub_neq_simple. auto.
      -- apply Reduced_Ord_remove in H.
         firstorder.
  -  assert(J:=lftl_noop v1 t lt). rewrite J; firstorder. 
Qed.

Lemma Not_In_Not_In_rev:forall(t:term)(tl:lTerm),
  ~ In t tl -> ~ In t (rev tl).
Proof.
  intros. assert(L:=Permutation_rev tl). apply (Permutation_Not_In _ _ t) in L;auto.
Qed.

Lemma Not_In_rev_Not_In:forall(t:term)(tl:lTerm),
  ~ In t (rev tl) -> ~ In t tl.
Proof.
  intros. assert(L:=Permutation_rev tl). symmetry in L. apply (Permutation_Not_In _ _ t ) in L;auto.
Qed.

Lemma Not_In_imply_Not_In_Reducing_lr:forall(v:var)(lt:lTerm),
  Reduced lt ->
  ~ In (V v) lt -> ~ In (V v) (Reducing_lr lt).
Proof.
  intros v lt L H. apply not_In_URducing. induction lt. auto.
  simpl in *. apply Decidable.not_or in H. destruct H. firstorder.
  destruct a;simpl;remember (AReducing_lr lt) as alt;unfold NReducing;simpl;apply Not_In_Not_In_rev.
  - destruct (In_dec (C n) (NReducing' alt)). apply n_add_In in i. rewrite i. apply not_In_remove. 
    apply Reduced_cons in L. firstorder.
    unfold NReducing in H1. now apply Not_In_rev_Not_In in H1.
    apply n_add_not_In in n0. rewrite n0. apply ListUtil.notin_app. split. 
    apply Reduced_cons in L. firstorder.
    now apply Not_In_rev_Not_In in H1.
    simpl. intro. destruct H1;auto.
  - destruct (In_dec (V v0) (NReducing' alt)). apply n_add_In in i. rewrite i. apply not_In_remove. 
    apply Reduced_cons in L. firstorder.
    unfold NReducing in H1. now apply Not_In_rev_Not_In in H1.
    apply n_add_not_In in n. rewrite n. apply ListUtil.notin_app. split. 
    apply Reduced_cons in L. firstorder.
    now apply Not_In_rev_Not_In in H1.
    simpl. intro. destruct H1;auto.
  - inversion L. inversion H1.
Qed.  
    

Lemma Not_In_imply_Not_In_Reducing_lr_Ord:forall(v:var)(lt:lTerm),
  Reduced lt ->
  ~ In (V v) lt -> ~ In (V v) (Reducing_lr_Ord lt).
Proof.
  intros. apply (Not_In_imply_Not_In_Reducing_lr v) in H. apply Not_In_Reducing_lr_Ord. auto. auto.
Qed.

Lemma Not_In_app_list_lTerm_imply_Not_In_Reducing_lr_Ord:forall(v:var)(llt:list lTerm),
  Forall Reduced llt ->
  ~ In (V v) (app_list_lTerm llt) -> ~ In (V v) (app_list_lTerm (map Reducing_lr_Ord llt)).
Proof.
  intros. 
  induction llt. auto. apply ListUtil.notin_app in H0. destruct H0.
  simpl. apply ListUtil.notin_app. split.
  apply Not_In_imply_Not_In_Reducing_lr_Ord. now apply Forall_inv in H.
  auto. apply Forall_inv_tail in H. firstorder.
Qed.
  



Lemma map_lftl_In_Ran_Not_In:forall(v v1:var)(t:term)(llt:list lTerm),
  Forall Reduced_Ord llt ->
  ~ In (V v) (app_list_lTerm llt) -> ~ var_of v t -> v <> v1 ->
  ~ In (V v) (app_list_lTerm (map (lftl (singleton_sub v1 t)) llt)).
Proof.
  intros. induction llt. auto.
  simpl. apply ListUtil.notin_app. split. 
  - apply Forall_inv in H. apply ListUtil.notin_app in H0. destruct H0.
    assert(L:=lftl_In_Ran_Not_In v v1 t a H H0 H1 H2). auto.
  - apply Forall_inv_tail in H. apply ListUtil.notin_app in H0. destruct H0. firstorder.
Qed.



Lemma Not_In_lTerm_In_after_sub:forall(lt:lTerm)(v1 v2:var)(t:term),
  Reduced_Ord lt ->
  ~ In (V v1) lt
  -> In (V v1) (lftl (singleton_sub v2 t) lt)
  -> var_of v1 t.
Proof.
  intros. induction lt.
  - inversion H1.
  - simpl in *. apply Decidable.not_or in H0. destruct H0. destruct H1.
    ++ inversion H;subst. inversion H3;subst. destruct a;try inversion H5;subst.
      -- simp lft in H1. inversion H1.
      -- simp lft in H1. destruct (eq_dec_var v2 v).
        * rewrite e in *. rewrite singleton_sub_eq_simple in H1. rewrite H1. simpl.
          destruct (eq_dec_var v1 v1). auto. now apply n.
        * rewrite singleton_sub_neq_simple in H1;auto. inversion H1. rewrite H10 in *.
          exfalso. now apply H0.
    ++ apply Reduced_Ord_remove in H. firstorder.
Qed.



Lemma Not_In_app_list_lTerm_In_after_sub:forall(llt:list lTerm)(v1 v2:var)(t:term),
  Forall Reduced_Ord llt ->
  ~ In (V v1) (app_list_lTerm llt) 
  -> In (V v1) (app_list_lTerm (map (lftl (singleton_sub v2 t)) llt))
  -> var_of v1 t.
Proof.
  intros. induction llt.
  - simpl in *. inversion H1.
  - simpl in *. apply ListUtil.notin_app in H0. destruct H0. apply in_app_iff in H1. destruct H1. 
    + apply Forall_inv in H. assert(J:=Not_In_lTerm_In_after_sub a v1 v2 t). firstorder.
    + apply Forall_inv_tail in H. firstorder.
Qed.

Lemma In_lftl_Ran_In:forall(v:var)(t:term)(lt:lTerm),
  In (V v) lt -> In t (lftl (singleton_sub v t) lt).
Proof.
  intros. induction lt. inversion H. simpl in H. destruct H; simpl.
  left. rewrite H. simp lft. now apply singleton_sub_eq_simple.
  firstorder.
Qed.

Lemma Not_In_In_neq{X:Type}:forall(x:X)(l:list X),
  ~ In x l -> (forall x1:X, In x1 l -> x <> x1).
Proof.
  intros. induction l. auto. simpl in *. apply Decidable.not_or in H. destruct H.
  destruct H0. rewrite H0 in H. intro. now apply H. firstorder.
Qed. 


Lemma Not_In_Not_In_sub:forall(v1 v2:var)(t:term)(lt:lTerm),
  Reduced_Ord lt ->
  v1 <> v2 -> In (V v2) lt ->
  ~ In (V v1) (lftl (singleton_sub v2 t) lt) -> ~ In (V v1) (t :: lt).
Proof.
  intros. simpl. apply LogicUtil.not_or. split. 
  - apply (In_lftl_Ran_In _ t lt) in H1 as H3. 
  assert(H4:=Not_In_In_neq (V v1) (lftl (singleton_sub v2 t) lt) H2 t). firstorder.
  - induction lt. auto. simpl in *. apply LogicUtil.not_or. split.
    + destruct H1.
      -- rewrite H1. intro. inversion H3. now apply H0.
      -- apply Decidable.not_or in H2. destruct H2. firstorder. 
         destruct a;auto. destruct (eq_dec_var v v1).
         ++ rewrite e in *. simp lft in H1. assert(L:=singleton_sub_neq_simple v2 v1). simp lft in H2.
            rewrite L in H2. intro. now apply H2. firstorder.
         ++ intro. inversion H4. now apply n.
         ++ intro. inversion H4.
    + apply Decidable.not_or in H2. destruct H2. destruct (In_dec (V v2) lt). 
      -- apply Reduced_Ord_remove in H. firstorder.
      -- apply Reduced_Ord_remove in H. assert(J:=singleton_sub_not_dom v2 lt t H n). rewrite J in H3.
         auto.
Qed.

Lemma Not_In_var_UReducing:forall(v:var)(lt:lTerm),
  ~ In (V v) (UReducing lt) -> ~ In (V v) lt.
Proof.
  intros. induction lt. auto. simpl. apply LogicUtil.not_or. split;simpl in H;
  destruct (term_beq_syn a T0) eqn:J.
  - apply term_beq_syn_true_iff in J. rewrite J. intro. inversion H0.
  - simpl in H. apply Decidable.not_or in H. destruct H. auto.
  - firstorder.
  - simpl in H. apply Decidable.not_or in H. destruct H. auto.
Qed.

Lemma Not_In_UReducing_var:forall(v:var)(lt:lTerm),
  ~ In (V v) lt -> ~ In (V v) (UReducing lt).
Proof.
  intros. induction lt. auto. simpl. destruct (term_beq_syn a T0) eqn:J.
  - apply term_beq_syn_true_iff in J. rewrite J in H. simpl in H. apply Decidable.not_or in H.
    destruct H. firstorder.
  - simpl in H. apply Decidable.not_or in H. destruct H. apply LogicUtil.not_or. split.
    auto. firstorder.
Qed.

Lemma notIn_NReducing' t l:
  ~ In t (NReducing' l) ->
  Nat.Even (count_occ term_beq_syn_dec l t).
Proof. 
  intros. 
  assert(H0:= count_NReducing'_1_0 l t). 
  destruct (Even_Odd_dec (count_occ term_beq_syn_dec l t)).
  - now apply count_occ_not_In in H0.
  - destruct o. exfalso. apply H. assert(J:=NReducing'_In t l). apply J. rewrite H1. 
    unfold Nat.Odd. exists x. auto.
Qed.


Lemma Not_var_of_Not_In_Reducing:forall(v:var)(t:term),
  ~ var_of v t -> ~ In (V v) (Reducing_lr [t]).
Proof.
  intros. unfold Reducing_lr.
  induction t;simpl.
  - destruct (NatUtil.beq_nat n 0);auto. intro. inversion H0. inversion H1. inversion H1.
  - intro. apply H. destruct H0. inversion H0. simpl. destruct (eq_dec_var v v). auto. 
    now apply n. inversion H0.
  - simpl in H. apply Decidable.not_or in H. destruct H. firstorder.
    rewrite AReducing_lr_term_to_lTerm_cons in *. 
    remember (term_to_lTerm t1) as at1. remember (term_to_lTerm t2) as at2. simpl in *.
    rewrite app_nil_r in *. apply Not_In_var_UReducing in H2. 
    apply Not_In_var_UReducing in H1. apply Not_In_UReducing_var.
    clear Heqat1 Heqat2. 
    unfold NReducing in *. apply Not_In_Not_In_rev.
    apply Not_In_rev_Not_In in H2. apply Not_In_rev_Not_In in H1.
    apply NReducing'_notIn. apply notIn_NReducing' in H1. apply notIn_NReducing' in H2.
    destruct H1. destruct H2. rewrite count_occ_app. rewrite H1. rewrite H2. exists(x+x0). lia.
Qed.

Lemma Not_In_Reducing_lr_remove:forall(v:var)(t:term)(lt:lTerm),
  Reduced (t::lt) ->
  (V v) <> t ->
  ~ In (V v) lt -> ~ In (V v) (Reducing_lr_Ord (t::lt)).
Proof.
  intros. apply Not_In_Reducing_lr_Ord. unfold Reducing_lr. 
  apply not_In_URducing. unfold NReducing. apply Not_In_Not_In_rev.
  apply not_In_Reduced. inversion H;subst. inversion H2;subst. 
  inversion H4;subst;simpl;apply Classical_Prop.and_not_or;split;auto.
  - apply AReduced_AReducing_idpt in H6. now rewrite H6.
  - apply AReduced_AReducing_idpt in H6. simpl. apply Classical_Prop.and_not_or.
    split. auto. now rewrite H6.
Qed.

Lemma Not_In_Reducing_lr_Ord_remove:forall(v:var)(t:term)(lt:lTerm),
  Reduced_Ord (t::lt) ->
  (V v) <> t ->
  ~ In (V v) lt -> ~ In (V v) (Reducing_lr_Ord (t::lt)).
Proof.
  intros. apply Not_In_Reducing_lr_Ord. unfold Reducing_lr. 
  apply not_In_URducing. unfold NReducing. apply Not_In_Not_In_rev.
  apply not_In_Reduced. inversion H;subst. inversion H2;subst. 
  inversion H4;subst;simpl;apply Classical_Prop.and_not_or;split;auto.
  - apply AReduced_AReducing_idpt in H8. now rewrite H8.
  - apply AReduced_AReducing_idpt in H8. now rewrite H8.
Qed.

Lemma var_Not_In_UReducing:forall(v:var)(lt:lTerm),
  ~ In (V v) (UReducing lt) -> ~ In (V v) lt.
Proof.
  intros. induction lt. auto. simpl in *. destruct (term_beq_syn a T0)eqn:L.
  - apply term_beq_syn_true_iff in L. rewrite L in *. apply Classical_Prop.and_not_or.
    split. intro. inversion H0. firstorder.
  - apply term_beq_syn_false_iff in L. apply Classical_Prop.and_not_or. apply not_in_cons in H.
    destruct H. split;auto.
Qed.


Lemma Not_In_Reducing_lr_Ord_cons:forall(v:var)(t:term)(lt:lTerm),
  Reduced [t] ->
  (V v) <> t ->
  ~ In (V v) (Reducing_lr_Ord lt) -> ~ In (V v)(Reducing_lr_Ord (t::lt)).
Proof.
  intros. apply Not_In_Reducing_lr_Ord. apply Not_In_Reducing_lr_Ord in H1.
  unfold Reducing_lr. unfold Reducing_lr in H1. apply var_Not_In_UReducing in H1.
  apply not_In_URducing. unfold NReducing in *. apply Not_In_Not_In_rev. 
  apply Not_In_rev_Not_In in H1.
  inversion H. inversion H2;subst;simpl.
  - destruct (In_dec (C n)((NReducing' (AReducing_lr lt)))).
    + apply n_add_In in i. rewrite i. apply not_In_remove. auto.
    + apply n_add_not_In in n0. rewrite n0. apply ListUtil.notin_app. split;auto.
      intro. inversion H5. inversion H6. inversion H6.
  - destruct (In_dec (V v0)((NReducing' (AReducing_lr lt)))).
    + apply n_add_In in i. rewrite i. apply not_In_remove. auto.
    + apply n_add_not_In in n. rewrite n. apply ListUtil.notin_app. split;auto.
      intro. inversion H5. now apply H0. inversion H6. 
Qed. 

Lemma Not_In_Reducing_lr_Ord_app:forall(v:var)(tl1 tl2:lTerm),
  ~ In (V v) (Reducing_lr_Ord tl1) -> ~ In (V v) (Reducing_lr_Ord tl2)
  -> ~ In (V v) (Reducing_lr_Ord (tl1++tl2)).
Proof.
  intros. apply Not_In_Reducing_lr_Ord. apply Not_In_Reducing_lr_Ord in H.
  apply Not_In_Reducing_lr_Ord in H0. unfold Reducing_lr in *.
  apply var_Not_In_UReducing in H. apply var_Not_In_UReducing in H0.
  apply not_In_URducing. unfold NReducing in *. apply Not_In_Not_In_rev. 
  apply Not_In_rev_Not_In in H. apply Not_In_rev_Not_In in H0.
  apply notIn_NReducing' in H. apply notIn_NReducing' in H0.
  apply NReducing'_notIn. destruct H. destruct H0.
  rewrite <- AReducing_lr_app. rewrite count_occ_app. rewrite H. rewrite H0.
  exists (x + x0). lia.
Qed.



Lemma Not_In_orig_Not_var_of_Not_In_sub:forall (v1 v2:var)(t:term)(lt:lTerm),
  Reduced_Ord lt -> 
  ~ In (V v1) lt -> ~ var_of v1 t -> ~ In (V v1) (Reducing_lr_Ord(lftl (singleton_sub v2 t) lt)).
Proof.
  intros. induction lt. auto. simpl in *.
  apply Decidable.not_or in H0. destruct H0. inversion H;subst. inversion H3;subst.
  inversion H5;subst;simp lft; apply Reduced_Ord_remove in H;firstorder.
  - apply Not_In_Reducing_lr_Ord_cons;auto. repeat try constructor. auto. inversion H7. auto.
  - destruct (eq_dec_var v2 v).
    + rewrite e. rewrite singleton_sub_eq_simple. 
      assert(t :: lftl (singleton_sub v t) lt = [t] ++ lftl (singleton_sub v t) lt). auto.
      rewrite H10. apply Not_In_Reducing_lr_Ord_app;auto.
      -- apply Not_In_Reducing_lr_Ord. apply Not_var_of_Not_In_Reducing. auto.
      -- now rewrite e in H8.
    + rewrite singleton_sub_neq_simple;auto. 
      apply Not_In_Reducing_lr_Ord_cons;auto. repeat try constructor. auto.
Qed.

Lemma Not_In_orig_Not_var_of_Not_In_sub_app_list_lTerm:forall (v1 v2:var)(t:term)(llt:list lTerm),
  Forall Reduced_Ord llt 
  -> ~ In (V v1) (app_list_lTerm llt) 
  -> ~ var_of v1 t 
  -> ~ In (V v1) (app_list_lTerm (map Reducing_lr_Ord(map (lftl (singleton_sub v2 t)) llt))).
Proof.
  intros. induction llt.
  - auto.
  - simpl. apply ListUtil.notin_app. split.
    + apply ListUtil.notin_app in H0. destruct H0. apply Forall_inv in H. apply Not_In_orig_Not_var_of_Not_In_sub;auto.
    + apply Forall_inv_tail in H. apply ListUtil.notin_app in H0. destruct H0. firstorder.
Qed.





Lemma Not_In_sub_Not_In_orig:forall(v1 v2:var)(t:term)(lt:lTerm),
  Reduced_Ord lt ->
  ~ In (V v1) (lftl (singleton_sub v2 t) lt) -> v1 <> v2 -> ~ var_of v1 t
  -> ~ In (V v1) lt.
Proof.
  intros. destruct (In_dec (V v2) lt).
  - induction lt. auto. simpl in *. apply LogicUtil.not_or.
    apply Decidable.not_or in H0. destruct H0. split.
    + inversion H;subst. inversion H4;subst. inversion H6;subst.
      -- auto.
      -- destruct i. 
        ++ inversion H9. subst. intro. inversion H11. now apply H1.
        ++ destruct (eq_dec_var v2 v). intro. inversion H11. subst. now apply H1.
           simp lft in H0. rewrite singleton_sub_neq_simple in H0;auto.
    + destruct i. 
      -- inversion H;subst. inversion H5;subst. apply NReduced_NoDup in H7. apply NoDup_cons_iff in H7.
         destruct H7. apply Reduced_Ord_remove in H. assert(J:=lftl_noop v2 t lt H H7).
         rewrite J in H3. auto.
      -- apply Reduced_Ord_remove in H. firstorder.
  - assert(L:=lftl_noop v2 t lt H n). rewrite L in H0. auto.
Qed.

Lemma steps_simpl_disjoint_var_and_others:forall(sys:problems_set),
  (forall v:var, In (V v) (app_list_lTerm (map fst (fst sys))) -> ~ In (V v) (app_list_lTerm (map fst (snd sys))))
  /\ Forall Reduced_Ord (map fst (snd sys)) /\ Forall Reduced_Ord (map fst (fst sys)) /\ app_list_lTerm (map snd (fst sys)) = []
  -> 
  (forall v:var, In (V v) (app_list_lTerm (map fst (fst (step sys)))) -> ~ In (V v) (app_list_lTerm (map fst (snd (step sys)))))
  /\ Forall Reduced_Ord (map fst (snd (step sys))) /\ Forall Reduced_Ord (map fst (fst (step sys))) /\ app_list_lTerm (map snd (fst (step sys))) = [].
Proof.
  intros. destruct H. destruct H0. destruct H1. repeat split.
  - intros. unfold step in *. 
    induction sys; simpl in *. destruct a.
    + simpl in *. inversion H3.
    + simpl in *. destruct (lTerm_eqv_bool (fst p) []) eqn:JJ;simpl in *. 
      apply H. apply ListUtil.in_appr. auto.
      destruct (problem_to_sub p) eqn:J. destruct p0.
      -- apply problem_to_sub_not_In in J as J1. apply problem_to_sub_not_var_of in J as J2.
        apply problem_to_sub_not_In in J as J4. 
        unfold problem_to_sub in J. destruct (a_var_in_lTerm (fst (rawP_to_reducedP p))) eqn:J3.
        ++ inversion J. subst. simpl in *. clear J. apply a_var_in_lTerm_In in J3. unfold lhs in *.
            unfold rhs in *.
            remember (lTerm_to_term (remove (V v0) (Reducing_lr_Ord (fst p ++ snd p)))) as t.
            apply Classical_Prop.and_not_or. split.
            --- umap_fst_comm.
                assert(H:=H v0). intro. inversion H4. rewrite H4 in *.
                apply In_app_list_lTerm_problem_term in H3. destruct H3.
                remember (fst x) as l.
                rewrite singleton_sub_eq_simple in *. clear J4. 
                assert(J0:=Not_In_lftl_sub l v0 t J2). apply In_Reducing_lr_Ord in H3. rewrite H6 in *.
                now apply J0 in H3.
            --- umap_fst_comm.
                assert (L:=H v). rewrite singleton_sub_eq_simple in *. clear J4.
                destruct (eq_dec_var v0 v).
                +++ rewrite e in *. apply In_app_list_lTerm_problem_term in H3.
                    destruct H3.
                    assert(J4:=Not_In_lftl_sub (fst x) _ _ J2). apply Not_In_Reducing_lr_Ord in J4.
                    now apply J4 in H3.
                +++ apply app_eq_nil in H2. destruct H2.
                    rewrite H2 in J3. rewrite app_nil_r in J3. apply Forall_inv in H1 as G3.
                    apply Reduced_Ord_Reducing_lr_Ord in G3. rewrite G3 in J3.
                    assert(L3:=ListUtil.in_appl (V v0) _ (app_list_lTerm (map fst a)) J3). 
                    assert(L1:=H v0). apply L1 in L3. clear L1. clear L G3.
                    apply (map_lftl_noop _ t) in L3 as L4;auto. rewrite L4.
                    assert(L5:=Reduced_Ord_Reducing_lr_Ord_app_list_lTerm (map fst b)).
                    rewrite L5;auto. 
                    apply H. destruct (In_dec (V v) (Reducing_lr_Ord (fst p ++ snd p))).
                    ----rewrite H2 in *. rewrite app_nil_r in *. 
                        assert(i2:= ListUtil.in_appl (V v)(fst p)(app_list_lTerm (map fst a))).
                        apply i2. apply Forall_inv in H1. assert(i3:=Reduced_Ord_Reducing_lr_Ord).
                        rewrite <- i3;auto.
                    ----rewrite H2 in *. rewrite app_nil_r in *.
                        clear L5 L4 L3 J1 J2. 
                        destruct (In_dec (V v)(app_list_lTerm (map fst a))).
                        ----- assert(L2:=ListUtil.in_appr (V v) (fst p) _ i). auto. 
                        ----- exfalso. destruct (In_dec (V v0) (app_list_lTerm (map fst a))).
                              * apply (In_app_list_lTerm_Ran_In _ t) in i. apply Forall_inv_tail in H1 as G3.
                                assert(K:=Not_In_app_list_lTerm_In_after_sub (map fst a) v v0 t G3 n1).
                                assert(~ var_of v t).
                                **  apply Forall_inv in H1. apply (remove_NReduced_Ord (V v0)) in H1 as G22.
                                    assert(L1:=Reduced_Ord_Reducing_lr_Ord (fst p) H1). rewrite L1 in Heqt.
                                    assert(L:=Not_In_tl_var_of v (remove (V v0) 
                                    (fst p)) G22). rewrite Heqt. apply L. apply not_In_remove. 
                                    rewrite L1 in n0. auto.
                                **  apply H5. apply K. assert(v <> v0). intro. now apply n.
                                    assert(L1:=map_lftl_In_Ran_Not_In v v0 t (map fst a) G3 n1 H5 H6).
                                    exfalso.
                                    cut (~
                                    In (V v) (app_list_lTerm (map (lftl (singleton_sub v0 t)) (map fst a)))
                                    ->
                                    ~
                                    In (V v) (app_list_lTerm (map Reducing_lr_Ord (map (lftl (singleton_sub v0 t)) (map fst a))))
                                    ). intros. apply H7 in L1. now apply L1 in H3.
                                    intros. clear H7 K i n1 n0 n H0 J3 H2 H1 H b.
                                    remember (map fst a) as llt. clear Heqllt.
                                    induction llt. auto.
                                    simpl in *. apply ListUtil.notin_app in L1. destruct L1.
                                    apply Forall_inv in G3 as G2. apply Forall_inv_tail in G3.
                                    apply ListUtil.notin_app. split.
                                    ++++++ clear IHllt H0. destruct (In_dec (V v0) a0).
                                          **** apply in_app_iff in H3. destruct H3.
                                              ***** assert(J:=Not_In_sub_Not_In_orig v v0 t a0 G2 H H6 H5).
                                                    assert(J1:=Not_In_orig_Not_var_of_Not_In_sub v v0 t a0 G2 J H5).
                                                    auto.
                                              ***** assert(J:=Not_In_sub_Not_In_orig v v0 t a0 G2 H H6 H5).
                                                    assert(J1:=Not_In_orig_Not_var_of_Not_In_sub v v0 t a0 G2 J H5). auto.
                                          **** rewrite singleton_sub_not_dom in *;auto.
                                                rewrite Reduced_Ord_Reducing_lr_Ord;auto. 
                                    ++++++ firstorder.
                              * apply Forall_inv_tail in H1.
                                apply (map_lftl_noop _ t) in n2. rewrite n2 in H3.
                                assert(L5:=Reduced_Ord_Reducing_lr_Ord_app_list_lTerm (map fst a)).
                                rewrite L5 in H3;auto. auto.
        ++ inversion J.
      -- apply H. auto.
  - apply steps_simpl_Reduced_fstp2. auto.
  - apply steps_simpl_Reduced_fstp1. auto.
  - apply steps_simpl_nil_sndps1. auto.
Qed.


Lemma steps_disjoint_In_Var:forall(ps:problems)(ps1 ps2:problems),
  steps (measure (problems_set_ready ps)) (problems_set_ready ps) = (ps1,ps2) ->
  (forall v:var, In (V v) (app_list_lTerm (map fst ps1)) -> ~ In (V v) (app_list_lTerm (map fst ps2)))
  /\ Forall Reduced_Ord (map fst ps2) /\ Forall Reduced_Ord (map fst ps1) /\ app_list_lTerm (map snd ps1) = [].
Proof.
  intros. assert(L:=step_invariant 
  (fun p=> (forall v:var, In (V v) (app_list_lTerm (map fst (fst p))) 
  -> ~ In (V v) (app_list_lTerm (map fst (snd p)))) /\
  Forall Reduced_Ord (map fst (snd p)) /\ Forall Reduced_Ord (map fst (fst p))
  /\ app_list_lTerm (map snd (fst p)) = [])
  (problems_set_ready ps) (measure (problems_set_ready ps))).
  rewrite H in L. simpl in L. apply L;clear H L.
  - split. intros. auto.
    split. auto. split. unfold rawPs_to_reducedPs. unfold rawP_to_reducedP.
    induction ps;simpl. auto. apply Forall_cons. apply Reducing_lr_Ord_Correct_Reduced_Ord.
    auto. unfold rawPs_to_reducedPs. unfold rawP_to_reducedP. induction ps. auto. 
    simpl. auto.
  - intros. apply steps_simpl_disjoint_var_and_others. auto.
Qed.

Lemma steps_simpl_single_variable_others:forall(sys:problems_set),
(forall v:var, In (V v) (app_list_lTerm (map fst (fst sys))) -> ~ In (V v) (app_list_lTerm (map fst (snd sys))))
/\ Forall Reduced_Ord (map fst (snd sys)) /\ Forall Reduced_Ord (map fst (fst sys)) /\ app_list_lTerm (map snd (fst sys)) = []
/\ Forall single_variable_lTerm_Prop (map fst (snd sys))
-> 
(forall v:var, In (V v) (app_list_lTerm (map fst (fst (step sys)))) -> ~ In (V v) (app_list_lTerm (map fst (snd (step sys)))))
/\ Forall Reduced_Ord (map fst (snd (step sys))) /\ Forall Reduced_Ord (map fst (fst (step sys))) /\ app_list_lTerm (map snd (fst (step sys))) = []
/\ Forall single_variable_lTerm_Prop (map fst (snd (step sys))).
Proof.
  intros. destruct H. destruct H0. destruct H1. destruct H2. repeat split.
  - assert(J:=steps_simpl_disjoint_var_and_others sys). destruct J;auto.
  - assert(J:=steps_simpl_disjoint_var_and_others sys). destruct J;auto. destruct H5. auto.
  - assert(J:=steps_simpl_disjoint_var_and_others sys). destruct J;auto. destruct H5. destruct H6. auto.
  - assert(J:=steps_simpl_disjoint_var_and_others sys). destruct J;auto. destruct H5. destruct H6. auto.
  - intros. unfold step. destruct sys. simpl in *.
    destruct p.
    + auto.
    + destruct (lTerm_eqv_bool (fst p) []). simpl. auto.
      destruct (problem_to_sub p) eqn:J.
      --destruct p2. apply problem_to_sub_not_var_of in J as L. apply problem_to_sub_not_In in J as L1.
        unfold problem_to_sub in J. destruct (a_var_in_lTerm (fst (rawP_to_reducedP p))) eqn:J1.
        ++ inversion J. clear J. simpl. remember (lTerm_to_term
            (remove (V v) (Reducing_lr_Ord (lhs p ++ rhs p)))) as t.
            constructor;unfold single_variable_lTerm_Prop;simpl.
            --- auto.
            --- umap_fst_comm. apply a_var_in_lTerm_In in J1. unfold rawP_to_reducedP in J1.
                simpl in J1. unfold lhs in J1. unfold rhs in J1. simpl in H2. apply app_eq_nil in H2.
                destruct H2. rewrite H2 in J1. rewrite app_nil_r in J1. simpl in H1. apply Forall_inv in H1 as J2.
                rewrite Reduced_Ord_Reducing_lr_Ord in J1;auto. simpl in H. rewrite H5 in *.
                assert(J3:=ListUtil.in_appl (V v) (fst p) (app_list_lTerm (map fst p1)) J1).
                apply H in J3. assert(J4:=map_lftl_noop v t (map fst p0) H0 J3). rewrite J4.
                clear J4 J3 J2 H6 Heqt H5 L1 L J1 H4 H2 H1 H H0. remember (map fst p0) as l. clear Heql.
                induction l;simpl. auto. apply Forall_cons. apply Forall_inv in H3.
                unfold single_variable_lTerm_Prop in H3. unfold single_variable_lTerm in H3.
                destruct (single_variable_lTerm_var a) eqn:J. apply single_variable_lTerm_var_simpl in J.
                rewrite J. unfold Reducing_lr_Ord. unfold Reducing_lr. unfold sort_term. unfold sort_varterm. 
                simpl. unfold var_to_Var. auto. inversion H3.
                apply Forall_inv_tail in H3. firstorder.
        ++ inversion J.
      -- auto.
Qed.



Lemma steps_single_variable_lTerm_Prop:forall(ps:problems)(ps1 ps2:problems),
  steps (measure (problems_set_ready ps)) (problems_set_ready ps) = (ps1,ps2) ->
  (forall v:var, In (V v) (app_list_lTerm (map fst ps1)) -> ~ In (V v) (app_list_lTerm (map fst ps2)))
/\ Forall Reduced_Ord (map fst ps2) /\ Forall Reduced_Ord (map fst ps1) /\ app_list_lTerm (map snd ps1) = []
/\ Forall single_variable_lTerm_Prop (map fst ps2).
Proof.
  intros. 
  assert(L:=step_invariant 
  (fun p=> (forall v:var, In (V v) (app_list_lTerm (map fst (fst p))) -> ~ In (V v) (app_list_lTerm (map fst (snd p))))
  /\ Forall Reduced_Ord (map fst (snd p))
  /\ Forall Reduced_Ord (map fst (fst p))
  /\ app_list_lTerm (map snd (fst p)) = []
  /\ Forall single_variable_lTerm_Prop (map fst (snd p)))
  (problems_set_ready ps) (measure (problems_set_ready ps))).
  rewrite H in L. simpl in L. apply L.
  - clear L. repeat split;auto;unfold problems_set_ready in H; unfold rawPs_to_reducedPs.
    + clear H. unfold rawP_to_reducedP. induction ps;simpl. auto. apply Forall_cons.
      apply Reducing_lr_Ord_Correct_Reduced_Ord. auto.
    + clear H. induction ps. auto. simpl. auto.
  - apply steps_simpl_single_variable_others.
Qed.



Lemma steps_simpl_NoDup_others:forall(sys:problems_set),
  (forall v:var, In (V v) (app_list_lTerm (map fst (fst sys))) -> ~ In (V v) (app_list_lTerm (map fst (snd sys))))
  /\ Forall Reduced_Ord (map fst (snd sys)) /\ Forall Reduced_Ord (map fst (fst sys)) /\ app_list_lTerm (map snd (fst sys)) = []
  /\ Forall single_variable_lTerm_Prop (map fst (snd sys)) /\ NoDup (map fst (snd sys))
  -> 
  (forall v:var, In (V v) (app_list_lTerm (map fst (fst (step sys)))) -> ~ In (V v) (app_list_lTerm (map fst (snd (step sys)))))
  /\ Forall Reduced_Ord (map fst (snd (step sys))) /\ Forall Reduced_Ord (map fst (fst (step sys))) /\ app_list_lTerm (map snd (fst (step sys))) = []
  /\ Forall single_variable_lTerm_Prop (map fst (snd (step sys))) /\ NoDup (map fst (snd (step sys))).
Proof.
  intros. destruct H. destruct H0. destruct H1. destruct H2. destruct H3. repeat split.
  - assert(J:=steps_simpl_single_variable_others sys). destruct J;auto.
  - assert(J:=steps_simpl_single_variable_others sys). destruct J;auto. destruct H6. auto.
  - assert(J:=steps_simpl_single_variable_others sys). destruct J;auto. destruct H6. destruct H7. auto.
  - assert(J:=steps_simpl_single_variable_others sys). destruct J;auto. destruct H6. destruct H7. destruct H8. auto.
  - assert(J:=steps_simpl_single_variable_others sys). destruct J;auto. destruct H6. destruct H7. destruct H8. auto.
  - unfold step. destruct sys. simpl in *. destruct p.
    + auto.
    + destruct(lTerm_eqv_bool (fst p) []). simpl. auto.
      destruct (problem_to_sub p) eqn:J.
      -- destruct p2. simpl. unfold problem_to_sub in J. 
         destruct (a_var_in_lTerm (fst (rawP_to_reducedP p))) eqn:J1.
         ++ apply a_var_in_lTerm_In in J1. unfold rawP_to_reducedP in J1.
            simpl in J1. unfold lhs in J1. unfold rhs in J1. simpl in H2. apply app_eq_nil in H2.
            destruct H2. rewrite H2 in J1. rewrite app_nil_r in J1. simpl in H1. apply Forall_inv in H1 as J2.
            rewrite Reduced_Ord_Reducing_lr_Ord in J1;auto. simpl in H. 
            assert(J3:=ListUtil.in_appl (V v0) (fst p) (app_list_lTerm (map fst p1)) J1).
            apply H in J3. inversion J. umap_fst_comm. clear J. 
            remember ((lTerm_to_term (remove (V v) (Reducing_lr_Ord (lhs p ++ rhs p))))) as t.
            rewrite H7 in *. assert(J4:=map_lftl_noop v t (map fst p0) H0 J3). rewrite J4.
            apply not_In_Var_lTerm_general in J3 as J5. 
            apply Reduced_Ord_Reducing_lr_Ord_app_list_lTerm in H0. rewrite H0.
            constructor. auto. auto.
         ++ inversion J.
      -- auto.
Qed.


Lemma steps_NoDup:forall(ps:problems)(ps1 ps2:problems),
  steps (measure (problems_set_ready ps)) (problems_set_ready ps) = (ps1,ps2) ->
  NoDup (map fst ps2).
Proof.
  intros. assert(L:=step_invariant 
  (fun p=> (forall v:var, In (V v) (app_list_lTerm (map fst (fst p))) -> ~ In (V v) (app_list_lTerm (map fst (snd p))))
  /\ Forall Reduced_Ord (map fst (snd p)) 
  /\ Forall Reduced_Ord (map fst (fst p)) 
  /\ app_list_lTerm (map snd (fst p)) = []
  /\ Forall single_variable_lTerm_Prop (map fst (snd p))
  /\ NoDup (map fst (snd p))
  )
  (problems_set_ready ps) (measure (problems_set_ready ps))).
  rewrite H in L. simpl in L. apply L.
  - clear L. repeat split;auto;unfold problems_set_ready in H; unfold rawPs_to_reducedPs.
    + clear H. unfold rawP_to_reducedP. induction ps;simpl. auto. apply Forall_cons.
      apply Reducing_lr_Ord_Correct_Reduced_Ord. auto.
    + clear H. induction ps. auto. simpl. auto.
    + constructor.
  - apply steps_simpl_NoDup_others.
Qed.


Lemma disjoint_In_var_sym:forall(v:var)(lt1 lt2:lTerm),
  (In (V v) lt2 -> ~ In (V v) lt1)
  ->
  (In (V v) lt1 -> ~ In (V v) lt2).
Proof.
  intros v lt1. induction lt1;intros.
  - inversion H0.
  - destruct(In_dec (V v) lt2);auto. firstorder.
Qed.

Lemma disjoint_In_var_sym_forall:forall (lt1 lt2:lTerm),
  (forall(v:var), In (V v) lt2 -> ~ In (V v) lt1)
  ->
  (forall(v:var), In (V v) lt1 -> ~ In (V v) lt2).
Proof.
  intros. destruct (In_dec (V v) lt2); firstorder.
Qed.

Lemma disjoint_In_term_sym_forall:forall (lt1 lt2:lTerm),
  (forall t, In t lt2 -> ~ In t lt1)
  ->
  (forall t, In t lt1 -> ~ In t lt2).
Proof.
  intros. destruct (In_dec t lt2); firstorder.
Qed.


Lemma steps_simpl_disjoint_var:forall(sys:problems_set),
Forall Reduced_Ord (map fst (fst sys))
/\ Forall Reduced_Ord (map fst (snd sys))
/\ Forall Reduced_Ord (map snd (snd sys))
/\ app_list_lTerm (map snd (fst sys)) = []
/\ (forall v:var, In (V v) (app_list_lTerm (map fst (fst sys))) 
     -> ~ In (V v) (app_list_lTerm (map fst (snd sys))))
/\ (forall v:var, In (V v) (app_list_lTerm (map fst (snd sys))) 
     -> ~ In (V v) (app_list_lTerm (map snd (snd sys))))
    
->
(forall v:var, In (V v) (app_list_lTerm (map fst (snd (step sys)))) 
     -> ~ In (V v) (app_list_lTerm (map snd (snd (step sys))))).
Proof.
  intros. destruct H. destruct H1. destruct H2. destruct H3. destruct H4. 
  intros. destruct sys. destruct p. simpl in *.
      + auto.
      + simpl in *. destruct (lTerm_eqv_bool (fst p) []). auto.
        destruct (problem_to_sub p)eqn:J.
        -- destruct p2. apply problem_to_sub_not_var_of in J as L5.  
           unfold problem_to_sub in J. destruct(a_var_in_lTerm
           (fst (rawP_to_reducedP p))) eqn:J2.
          ++ inversion J; subst. clear J. simpl in *. destruct H0.
            --- inversion H0. rewrite H7 in *. clear H0 H7. apply ListUtil.notin_app.
                split.
                ** apply Forall_inv in H. apply Reduced_Ord_Reducing_lr_Ord in H.
                   rewrite <- H. assert(K:=Not_In_Reduced_Ord_lTerm (fst p) v). auto. 
                ** remember (lTerm_to_term
                   (remove (V v) (Reducing_lr_Ord (lhs p ++ rhs p)))) as t. clear H1.
                   clear H4 H5.
                   induction p0. auto. simpl. apply ListUtil.notin_app. split.
                   *** apply Not_In_Reducing_lr_Ord. apply Not_In_lftl_sub.
                       assert(Reduced_Ord (Reducing_lr_Ord (lhs p ++ rhs p))).
                       apply Reducing_lr_Ord_Correct_Reduced_Ord.
                       apply (remove_NReduced_Ord (V v)) in H0.
                       assert(K:=Not_In_Reduced_Ord_lTerm (lhs p ++ rhs p) v).
                       assert(L:=Not_In_tl_var_of v 
                       (remove (V v) (Reducing_lr_Ord (lhs p ++ rhs p))) H0 K). subst. auto.
                   *** simpl in H2. apply Forall_inv_tail in H2. auto.
            --- destruct (eq_dec_var v v0).
                +++ rewrite e in *. clear e. apply ListUtil.notin_app.
                    split.
                    ** apply Forall_inv in H. apply Reduced_Ord_Reducing_lr_Ord in H.
                      rewrite <- H. assert(K:=Not_In_Reduced_Ord_lTerm (fst p) v0). auto. 
                    ** remember (lTerm_to_term
                      (remove (V v0) (Reducing_lr_Ord (lhs p ++ rhs p)))) as t. clear H1 H2.
                      clear H4 H5 H0.
                      induction p0. auto. simpl. apply ListUtil.notin_app. split.
                      *** apply Not_In_Reducing_lr_Ord. apply Not_In_lftl_sub.
                          assert(Reduced_Ord (Reducing_lr_Ord (lhs p ++ rhs p))).
                          apply Reducing_lr_Ord_Correct_Reduced_Ord.
                          apply (remove_NReduced_Ord (V v0)) in H0.
                          assert(K:=Not_In_Reduced_Ord_lTerm (lhs p ++ rhs p) v0).
                          assert(L:=Not_In_tl_var_of v0
                          (remove (V v0) (Reducing_lr_Ord (lhs p ++ rhs p))) H0 K). subst. auto.
                      *** auto.
                +++ apply ListUtil.notin_app. split.
                    ** umap_fst_comm. assert(L:=H4 v). apply disjoint_In_var_sym in L.
                      *** apply ListUtil.notin_app in L. destruct L.
                          apply not_In_remove. auto.
                      *** clear L. remember (lTerm_to_term
                      (remove (V v0) (Reducing_lr_Ord (lhs p ++ rhs p)))) as t.
                      apply a_var_in_lTerm_In in J2. apply app_eq_nil in H3. destruct H3.
                      unfold rhs in *. rewrite H3 in *. rewrite app_nil_r in *.
                      unfold lhs in *. apply Forall_inv in H. apply Reduced_Ord_Reducing_lr_Ord in H.
                      rewrite H in J2. assert(J3:=ListUtil.in_appl (V v0) _ (app_list_lTerm (map fst p1)) J2).
                      apply H4 in J3. assert(J4:=map_lftl_noop v0 t _ H1 J3). 
                      rewrite J4 in *.
                      apply Reduced_Ord_Reducing_lr_Ord_app_list_lTerm in H1. rewrite H1 in H0.
                      auto.
                    ** remember (lTerm_to_term
                      (remove (V v0) (Reducing_lr_Ord (lhs p ++ rhs p)))) as t.

                      apply a_var_in_lTerm_In in J2 as K2. apply app_eq_nil in H3. destruct H3.
                      unfold rhs in *. rewrite H3 in *. rewrite app_nil_r in *.
                      unfold lhs in *. apply Forall_inv in H. apply Reduced_Ord_Reducing_lr_Ord in H as K.
                      rewrite K in *. assert(J3:=ListUtil.in_appl (V v0) _ (app_list_lTerm (map fst p1)) K2).
                      apply H4 in J3. umap_fst_comm.
                      
                      assert(J4:=map_lftl_noop v0 t _ H1 J3). rewrite J4 in *.
                      apply Reduced_Ord_Reducing_lr_Ord_app_list_lTerm in H1. 
                      rewrite H1 in *. apply H5 in H0 as K4. umap_snd_comm.
                      
                      assert(L:=disjoint_In_var_sym_forall _ _ H4). apply L in H0.
                      apply ListUtil.notin_app in H0. destruct H0.
                      assert(~ In (V v) (remove (V v0)(fst p))). apply not_In_remove. auto.
                      assert(Reduced_Ord (remove (V v0) (fst p))).
                      {apply remove_NReduced_Ord. auto. }
                      assert(L4:=Not_In_tl_var_of v _ H9 H8). rewrite <- Heqt in L4.
                      assert(L3:=Not_In_orig_Not_var_of_Not_In_sub_app_list_lTerm
                      v v0 t _ H2 K4 L4). auto.
          ++ inversion J.
        -- auto.
Qed.



Lemma steps_idpt_ps2:forall(ps:problems)(ps1 ps2:problems),
  steps (measure (problems_set_ready ps)) (problems_set_ready ps) = (ps1,ps2) ->
  (forall v:var, In (V v) (app_list_lTerm (map fst ps2)) -> ~ In (V v) (app_list_lTerm (map snd ps2))).
Proof.
  intros. assert(L:=step_invariant 
  (fun p => 
     Forall Reduced_Ord (map fst (fst p)) 
  /\ Forall Reduced_Ord (map fst (snd p))
  /\ Forall Reduced_Ord (map snd (snd p))
  /\ app_list_lTerm (map snd (fst p)) = []
  /\ (forall v:var, In (V v) (app_list_lTerm (map fst (fst p))) 
     -> ~ In (V v) (app_list_lTerm (map fst (snd p))))
  /\ (forall v:var, In (V v) (app_list_lTerm (map fst (snd p))) 
     -> ~ In (V v) (app_list_lTerm (map snd (snd p)))))
  (problems_set_ready ps) (measure (problems_set_ready ps))).
  rewrite H in L. simpl in L. apply L;clear L.
  - repeat split; auto. 
    + clear H. unfold rawP_to_reducedP. induction ps;simpl. auto. apply Forall_cons.
      apply Reducing_lr_Ord_Correct_Reduced_Ord. auto.   
    + clear H H0. unfold rawPs_to_reducedPs. unfold rawP_to_reducedP. induction ps;simpl. auto.
      auto.
  - intros. repeat split.
      ***** apply steps_simpl_Reduced_fstp1. destruct H1. auto. 
      ***** apply steps_simpl_Reduced_fstp2. destruct H1. destruct H2. auto.
      ***** apply steps_simpl_Reduced_fstp1_sndp2. destruct H1. destruct H2. now split.
      ***** apply steps_simpl_nil_sndps1. destruct H1. destruct H2. destruct H3. destruct H4. auto.
      ***** apply steps_simpl_disjoint_var_and_others. destruct H1. destruct H2. destruct H3. destruct H4. now repeat split.
      ***** apply steps_simpl_disjoint_var. auto.
  - auto. 
Qed.
      


Lemma In_single_variable_lTerm_Prop_False_const:forall(n:nat)(llt:list lTerm),
  Forall single_variable_lTerm_Prop llt -> In (C n) (app_list_lTerm llt) -> False.
Proof.
  intros. induction llt.
  - inversion H0.
  - simpl in *. apply in_app_iff in H0. destruct H0. 
    + apply Forall_inv in H.
      unfold single_variable_lTerm_Prop in H. unfold single_variable_lTerm in H.
      destruct (single_variable_lTerm_var a)eqn:J. apply single_variable_lTerm_var_simpl in J.
      rewrite J in H0. inversion H0. inversion H1. inversion H1. inversion H.
    + apply Forall_inv_tail in H. firstorder.
Qed.


Lemma In_single_variable_lTerm_Prop_False_oplus:forall(t1 t2:term)(llt:list lTerm),
  Forall single_variable_lTerm_Prop llt -> In (t1+'t2) (app_list_lTerm llt) -> False.
Proof.
  intros. induction llt.
  - inversion H0.
  - simpl in *. apply in_app_iff in H0. destruct H0. 
    + apply Forall_inv in H.
      unfold single_variable_lTerm_Prop in H. unfold single_variable_lTerm in H.
      destruct (single_variable_lTerm_var a)eqn:J. apply single_variable_lTerm_var_simpl in J.
      rewrite J in H0. inversion H0. inversion H1. inversion H1. inversion H.
    + apply Forall_inv_tail in H. firstorder.
Qed.

Lemma steps_disjoint_In:forall(ps:problems)(ps1 ps2:problems),
  steps (measure (problems_set_ready ps)) (problems_set_ready ps) = (ps1,ps2) ->
  disjoint_In (app_list_lTerm (map fst ps2)) (app_list_lTerm (map snd ps2)).
Proof.
  intros. assert(L:=step_invariant 
  (fun p=> 
  (forall v:var, In (V v) (app_list_lTerm (map fst (fst p))) -> ~ In (V v) (app_list_lTerm (map fst (snd p))))
  /\ Forall Reduced_Ord (map fst (snd p)) 
  /\ Forall Reduced_Ord (map fst (fst p)) 
  /\ Forall Reduced_Ord (map snd (snd p))
  /\ app_list_lTerm (map snd (fst p)) = []
  /\ Forall single_variable_lTerm_Prop (map fst (snd p)) 
  /\ NoDup (map fst (snd p))
  /\ (forall v:var, In (V v) (app_list_lTerm (map fst (snd p))) -> ~ In (V v) (app_list_lTerm (map snd (snd p))))
  /\ disjoint_In (app_list_lTerm (map fst (snd p))) (app_list_lTerm (map snd (snd p)))
  )
  (problems_set_ready ps) (measure (problems_set_ready ps))).
  rewrite H in L. simpl in L. apply L.
  - clear L. repeat split;auto;unfold problems_set_ready in H; unfold rawPs_to_reducedPs.
    + clear H. unfold rawP_to_reducedP. induction ps;simpl. auto. apply Forall_cons.
      apply Reducing_lr_Ord_Correct_Reduced_Ord. auto.
    + clear H. induction ps. auto. simpl. auto.
    + constructor.
    + now unfold disjoint_In.
  - repeat split;clear L H;destruct H0;destruct H0;destruct H1; 
    destruct H2; destruct H3; destruct H4;destruct H5;destruct H6.
    + apply steps_simpl_disjoint_var_and_others. now repeat split.
    + apply steps_simpl_Reduced_fstp2. auto.
    + apply steps_simpl_Reduced_fstp1. auto.
    + apply steps_simpl_Reduced_fstp1_sndp2. auto.
    + apply steps_simpl_nil_sndps1. auto.
    + apply steps_simpl_single_variable_others. now repeat split.
    + apply steps_simpl_NoDup_others. now repeat split.    
    + apply steps_simpl_disjoint_var. now repeat split.
    + unfold disjoint_In in *. intros. assert(L:=steps_simpl_single_variable_others sys).
      destruct L. repeat split;auto. destruct H10. destruct H11. destruct H12. 
      assert(forall v : var,
      In (V v) (app_list_lTerm (map fst (snd (step sys)))) ->
      ~ In (V v) (app_list_lTerm (map snd (snd (step sys))))). apply steps_simpl_disjoint_var.
      repeat split;auto. 
      assert(Forall single_variable_lTerm_Prop (map fst (snd (step sys)))).
      apply steps_simpl_single_variable_others. now repeat split.
      clear H H0 H1 H2 H3 H4 H5 H6 H9 H10 H11 H12 H13.
      assert(L:=disjoint_In_term_sym_forall _ _ H7).
      destruct t.
      -- assert(L1:=In_single_variable_lTerm_Prop_False_const _ _ H15 H8). inversion L1.
      -- auto.
      -- assert(L1:=In_single_variable_lTerm_Prop_False_oplus _ _ _ H15 H8). inversion L1.
Qed.


(*
Important theorem about transforming function correctly transform the original problems to solved form
*)
Theorem rawPs_to_solvedPs_solved_form:forall(ps:problems) (ps1 ps2:problems),
  steps (measure (problems_set_ready ps)) (problems_set_ready ps) = (ps1,ps2) ->
  solved_form ps2.
Proof.
  intros. 
  apply steps_NoDup in H as J.
  apply steps_disjoint_In_Var in H as J1. destruct J1. destruct H1. destruct H2.
  apply steps_single_variable_lTerm_Prop in H as J2. destruct J2. destruct H5. destruct H6. destruct H7.
  apply steps_Reduced_Out in H as J3. inversion J3.
  apply steps_disjoint_In in H. 
  clear J3 H10 H4 H5 H6.
  constructor;try repeat split.
  - auto.
  - auto.
  - auto.
  - auto. 
Qed.




Lemma solves_problems_solves_Rproblems:forall(ps:problems)(sb:sub),
  solves_problems sb ps -> solves_problems sb (Rproblems ps).
Proof.
  intros. induction ps. auto. ufps. apply Forall_cons.
  - apply Forall_inv in H as H1. clear H IHps. destruct a. simpl in *.
    assert(J:=Reducing_lr_Ord_lftl_comm l sb).
    assert(J1:=Reducing_lr_Ord_lftl_comm l0 sb). apply lr_sym in J.
    assert(J2:=Reducing_lr_Ord_Correct_eqv (lftl sb l)).
    assert(J3:=Reducing_lr_Ord_Correct_eqv (lftl sb l0)).
    assert(H0:=lr_trans _ _ _ H1 J3). apply lr_sym in H0.
    assert(H2:=lr_trans _ _ _ H0 J2). clear H1 J2 J3 H0. 
    assert(H1:=lr_trans _ _ _ H2 J). apply lr_sym in H1. apply lr_sym in J1. 
    assert(H3:=lr_trans _ _ _ H1 J1). auto.
  - apply Forall_inv_tail in H. auto.
Qed.

Lemma solves_Rproblems_solves_problems:forall(ps:problems)(sb:sub),
  solves_problems sb (Rproblems ps) -> solves_problems sb ps.
Proof.
  intros. induction ps. auto. ufps. apply Forall_cons.
  - apply Forall_inv in H as H1. clear H IHps. destruct a. simpl in *.
    assert(J:=Reducing_lr_Ord_lftl_comm l sb).
    assert(J1:=Reducing_lr_Ord_lftl_comm l0 sb). apply lr_sym in J.
    assert(J2:=Reducing_lr_Ord_Correct_eqv (lftl sb l)).
    assert(J3:=Reducing_lr_Ord_Correct_eqv (lftl sb l0)).
    assert(H0:=lr_trans _ _ _ J2 J). 
    assert(H2:=lr_trans _ _ _ H0 H1).  
    assert(H4:=lr_trans _ _ _ H2 J1). apply lr_sym in J3.
    assert(H3:=lr_trans _ _ _ H4 J3). auto.
  - apply Forall_inv_tail in H. auto.
Qed.

Lemma singleton_solved_form:forall(p:problem)(v:var),
  a_var_in_lTerm (fst (rawP_to_reducedP p)) = Some v
  -> solved_form [([V v], (remove (V v) (Reducing_lr_Ord (lhs p ++ rhs p))))].
Proof.
  intros. unfold rawP_to_reducedP in H. simpl in H. 
  assert (Reduced_Ord (remove (V v) (Reducing_lr_Ord (lhs p ++ rhs p)))).
  apply remove_NReduced_Ord. apply Reducing_lr_Ord_Correct_Reduced_Ord.
  inversion H0;subst. inversion H1;subst.
  repeat try constructor;simpl;auto.
  unfold disjoint_In. intros. simpl in H6. inversion H6.
  rewrite <- H7 in *. rewrite app_nil_r. apply Not_In_Reduced_Ord_lTerm. inversion H7.
Qed.

Lemma solves_apply_sub_compose_simple_singleton:forall (p:problem)(sb1 sb2:sub),
  solves_problem sb1 (apply_sub_problem sb2 p) -> solves_problem (compose_sub sb1 sb2) p.
Proof.
  intros. ufp. now repeat rewrite compose_sub_lft.
Qed.

Lemma compose_solves_apply_sub_simple_singleton:forall (p:problem)(sb1 sb2:sub),
  solves_problem (compose_sub sb1 sb2) p -> solves_problem sb1 (apply_sub_problem sb2 p).
Proof.
  intros. ufp. now repeat rewrite compose_sub_lft in H.
Qed. 

Lemma solves_apply_sub_compose_simple:forall (ps:problems)(sb1 sb2:sub),
  solves_problems sb1 (apply_sub_problems sb2 ps) -> solves_problems (compose_sub sb1 sb2) ps.
Proof.
  intros. ufps. induction ps. auto. simpl in *. apply Forall_cons.
  - clear IHps. apply Forall_inv in H. ufp. repeat rewrite compose_sub_lft. auto.
  - apply Forall_inv_tail in H. firstorder.
Qed.

Lemma compose_solves_apply_sub_simple:forall (ps:problems)(sb1 sb2:sub),
  solves_problems (compose_sub sb1 sb2) ps -> solves_problems sb1 (apply_sub_problems sb2 ps) .
Proof.
  intros. ufps. induction ps. auto. simpl in *. apply Forall_cons.
  - clear IHps. apply Forall_inv in H. ufp. repeat rewrite compose_sub_lft in H. auto.
  - apply Forall_inv_tail in H. firstorder.
Qed.



Lemma solves_problems_cons:forall(p:problem)(ps:problems)(sb:sub),
  solves_problems sb (p::ps) <-> solves_problem sb p /\ solves_problems sb ps.
Proof.
  split;intros. 
  ufps. apply Forall_inv in H as H1. apply Forall_inv_tail in H. now split.
  ufps. destruct H. now apply Forall_cons.
Qed.

Lemma sub_v_eqv_t:forall(sb1 sb2:sub)(t:term),
  (forall v:var, sb1 v == sb2 v) -> lft sb1 t == lft sb2 t.
Proof.
  intros. induction t;simp lft. apply eqv_ref. rewrite IHt1. rewrite IHt2.
  apply eqv_ref.
Qed.  

Lemma sub_v_eqv_t_any:forall(sb1 sb2:sub)(t1 t2:term),
  (forall v:var, sb1 v == sb2 v) -> t1 == t2 ->lft sb1 t1 == lft sb2 t2.
Proof.
  intros. induction H0;simp lft;assert(H1:= sub_v_eqv_t sb1 sb2 x H);
  try assert(H2:= sub_v_eqv_t sb1 sb2 y H); try assert(H3:= sub_v_eqv_t sb1 sb2 z H);
  try rewrite H1;try rewrite H2; try rewrite H3.
  - rewrite eqvA. reflexivity.
  - rewrite eqvC. reflexivity.
  - rewrite eqvU. reflexivity.
  - rewrite eqvN. reflexivity.
  - reflexivity.
  - rewrite <- H1. symmetry. auto. 
  - rewrite <- H1. rewrite IHeqv1. rewrite <- H2. auto.
  - rewrite <- H1. rewrite IHeqv1. rewrite <- H2. rewrite IHeqv2. reflexivity.
Qed.

Lemma eqv_to_lTerm_eqv:forall(t1 t2:term),
  t1 == t2 <-> [t1] =l= [t2].
Proof.
  split;intros.
  - assert(J:=lr_eqv_add1 t1 t2 nil nil H). now simpl in J.
  - apply lTerm_eqv_ok in H. rewrite lTerm_eqv_t_singleton. 
    symmetry. rewrite lTerm_eqv_t_singleton. now symmetry.
Qed.

Lemma sub_v_eqv_tl:forall(sb1 sb2:sub)(tl:lTerm),
  (forall v:var, sb1 v == sb2 v) -> lftl sb1 tl =l= lftl sb2 tl.
Proof.
  intros. induction tl;simp lft. simpl. apply lr_relf.
  simpl. 
  assert(L:=lr_compat [lft sb1 a] [lft sb2 a] (lftl sb1 tl) (lftl sb2 tl)).
  simpl in L. apply L;auto. apply (sub_v_eqv_t _ _ a) in H. apply eqv_to_lTerm_eqv.
  auto.
Qed.

Lemma sub_v_eqv_tl_any:forall(sb1 sb2:sub)(tl1 tl2:lTerm),
  (forall v:var, sb1 v == sb2 v) -> tl1 =l= tl2 -> lftl sb1 tl1 =l= lftl sb2 tl2.
Proof.
  intros. induction H0;simpl;unfold lftl. 
  - repeat rewrite map_app. rewrite map_cons. unfold T0. simp lft.
    assert(J1:=sub_v_eqv_tl _ _ ll H). assert(J2:=sub_v_eqv_tl _ _ lr H).
    assert(lftl sb1 lr =l= T0::lftl sb2 lr).
    assert([T0] =l= nil). assert(J:=lr_T0 nil nil). simpl in J. now apply lr_sym.
    apply lr_sym in H0.
    assert(L:=lr_compat nil [T0] _ _ H0 J2). simpl in L. auto.
    assert(L:=lr_compat _ _ _ _ J1 H0). unfold T0 in L. unfold lftl in L. auto.
  - repeat rewrite map_app. repeat rewrite map_cons.
    assert(J1:=sub_v_eqv_tl _ _ l1 H). assert(J2:=sub_v_eqv_tl _ _ l2 H).
    assert(J3:=sub_v_eqv_t_any sb1 sb2 x y H H0). apply eqv_to_lTerm_eqv in J3.
    assert(J4:=sub_v_eqv_tl sb1 sb2 l2 H).
    assert(J5:=sub_v_eqv_tl sb1 sb2 l1 H).
    assert(L:=lr_compat [lft sb1 x][lft sb2 y] (map (lft sb1) l2)(map (lft sb2) l2) J3 J4).
    assert(L2:=lr_compat _ _ _ _ J5 L). simpl in L2. unfold lftl in L2. auto.
  - rewrite map_app. unfold T0. simp lft. 
    apply lr_N.
  - apply lr_perm in H0. apply (lTerm_eqv_lftl sb1) in H0.
    assert(J2:=sub_v_eqv_tl sb1 sb2 y H).
    assert(J3:=lr_trans _ _ _ H0 J2). unfold lftl in J3. auto.
  - repeat rewrite map_app. unfold lftl in *. apply lr_compat;auto.
  - assert(J2:=sub_v_eqv_tl sb1 sb2 l1 H). assert(J3:=sub_v_eqv_tl sb1 sb2 l2 H).
    unfold lftl in *. apply lr_sym in J3.
    assert(L:=lr_trans _ _ _ IHlTerm_eqv1 J3).
    assert(L1:=lr_trans _ _ _ L IHlTerm_eqv2). auto.
  - apply lr_sym. 
    assert(J2:=sub_v_eqv_tl sb1 sb2 l1 H).
    assert(J3:=sub_v_eqv_tl sb1 sb2 l2 H). apply lr_sym in J2. unfold lftl in *.
    assert(L:=lr_trans _ _ _ J2 IHlTerm_eqv). apply lr_sym in J3.
    assert(L1:=lr_trans _ _ _ L J3). auto.
  - assert(J2:=sub_v_eqv_tl sb1 sb2 l1 H). auto.
  - simp lft. assert(J:=sub_v_eqv_t sb1 sb2 t1 H).
    assert(J1:=sub_v_eqv_t sb1 sb2 t2 H). 
    assert(J2:=lr_oplus (lft sb1 t1) (lft sb1 t2)).
    assert(L:=lr_trans _ _ [lft sb2 t1; lft sb2 t2] J2). apply L.
    assert(L1:=lr_compat [lft sb1 t1][lft sb2 t1][lft sb1 t2][lft sb2 t2]).
    simpl in L1. apply L1;apply eqv_to_lTerm_eqv;auto.
Qed.

    

Lemma sub_v_eqv_solves_problem:forall(sb1 sb2:sub)(p:problem),
  (forall v:var, sb1 v == sb2 v) -> solves_problem sb1 p -> solves_problem sb2 p.
Proof.
  intros. ufp. unfold lftl in *. 
  assert (L:=sub_v_eqv_tl _ _ (lhs p) H).
  assert (L1:=sub_v_eqv_tl _ _ (rhs p) H).
  unfold lftl in *. assert(J:=lr_trans _ _ _ H0 L1). apply lr_sym in L.
  assert(J1:=lr_trans _ _ _ L J). auto.
Qed.

Lemma sub_v_eqv_solves_problems:forall(sb1 sb2:sub)(ps:problems),
  (forall v:var, sb1 v == sb2 v) -> solves_problems sb1 ps -> solves_problems sb2 ps.
Proof.
  intros. induction ps.
  - now ufps.
  - ufps. apply Forall_cons. 
    + clear IHps. apply Forall_inv in H0. 
      assert(L:= sub_v_eqv_solves_problem sb1 sb2 a H). ufp. auto.
    + apply Forall_inv_tail in H0. auto.
Qed.

Lemma unifiers_preserve_singleton:forall(sb:sub)(p:problem)(v:var),
  a_var_in_lTerm (fst (rawP_to_reducedP p)) = Some v ->
  solves_problem sb p -> 
  solves_problem sb ([V v], (remove (V v) (Reducing_lr_Ord (lhs p ++ rhs p)))).
Proof.
  intros. destruct p. ufp. apply lTerm_eqv_lTerm_eqv_nil in H0. 
  apply lTerm_eqv_same_side_nil. unfold lftl in *.
  rewrite <- map_app in H0. assert([lft sb (V v)] ++
  map (lft sb) (remove (V v) (Reducing_lr_Ord (l ++ l0))) =
  lftl sb (V v :: (remove (V v) (Reducing_lr_Ord (l ++ l0))))).
  simpl. auto. rewrite H1. clear H1. apply lr_sym in H0.
  assert(L:=lr_trans _ _ (lftl sb (V v :: remove (V v) (Reducing_lr_Ord (l ++ l0)))) H0).
  apply lr_sym. apply L. clear L. assert(J:=lTerm_eqv_lftl). unfold lftl in *.
  apply J. clear J. assert(J:=Reducing_lr_Ord_Correct_eqv (l ++ l0)).
  assert(L:=lr_trans _ _ (V v :: remove (V v) (Reducing_lr_Ord (l ++ l0))) J).
  apply L. apply a_var_in_lTerm_In in H. 
  clear L J H0. apply lr_perm. apply Permutation_In_cons_remove. auto.
Qed.



Lemma solved_form_unifiers_equal:forall(v:var)(sb sb':sub)(p:problem),
  solved_form [p] -> solves_problem sb p -> problem_to_sub p = Some (v,sb') ->
  (forall v':var, (compose_sub sb sb') v' == sb v').
Proof.
  intros. unfold problem_to_sub in H1. 
  destruct (a_var_in_lTerm (fst (rawP_to_reducedP p))) eqn:J.
  inversion H1;subst.
  - clear H1. destruct (eq_dec_var v v').
    + rewrite e in *. remember (lTerm_to_term
      (remove (V v') (Reducing_lr_Ord (lhs p ++ rhs p)))) as t.
      unfold compose_sub. rewrite singleton_sub_eq_simple. 
      assert(J1:=unifiers_preserve_singleton sb p _ J H0). rewrite Heqt in *. ufp.
      assert(J2:=lftl_lft_correct sb (remove (V v') (Reducing_lr_Ord (lhs p ++ rhs p)))).
      symmetry in J2. rewrite J2. clear J2. apply listEqv_eqv_sound in J1.
      rewrite <- J1. simp lft. symmetry. apply lTerm_eqv_t_singleton.
    + remember (lTerm_to_term
      (remove (V v) (Reducing_lr_Ord (lhs p ++ rhs p)))) as t.
      unfold compose_sub. rewrite singleton_sub_neq_simple;auto. now simp lft.
  - inversion H1.
Qed.


Lemma problem_to_sub_simpl_helper:forall (v:var)(p:problem),
  In (V v) (Reducing_lr_Ord (lhs p ++ rhs p)) ->
  Reducing_lr_Ord (V v :: remove (V v) (Reducing_lr_Ord (lhs p ++ rhs p)))
    = Reducing_lr_Ord (lhs p ++ rhs p).
Proof.
  intros v p KK. remember (lhs p ++ rhs p) as l.
  assert(Reduced_Ord (Reducing_lr_Ord l)). apply Reducing_lr_Ord_Correct_Reduced_Ord.
  clear Heql. apply (remove_NReduced_Ord (V v)) in H as H1.
  inversion H1;subst. inversion H0;subst.
  assert(Reduced (V v :: remove (V v) (Reducing_lr_Ord l))).
  { repeat constructor;auto. apply Not_In_Reduced_Ord_lTerm. }
  unfold Reducing_lr_Ord at 1 3. 
  apply Permutation_sort_same. apply Reduced_Reducing in H6 as J.
  rewrite J. clear J H1 H0 H2 H3 H4 H5 H6. 
  assert(Permutation (Reducing_lr l) (Reducing_lr_Ord l)).
  unfold Reducing_lr_Ord. assert(L:=sort_ltSorted_Permutation (Reducing_lr l)).
  apply L. assert(Reduced (Reducing_lr l)). apply Reducing_lr_Correct_Reduced.
  now inversion H0. rewrite H0. apply Permutation_In_cons_remove in KK. symmetry. auto.
Qed.


Lemma a_var_in_lTerm_transform:forall(v:var)(p:problem),
  a_var_in_lTerm (fst (rawP_to_reducedP p)) = Some v ->
  a_var_in_lTerm (Reducing_lr_Ord (V v ::remove(V v)(Reducing_lr_Ord (lhs p ++ rhs p)))) = Some v.
Proof.
  intros. apply a_var_in_lTerm_In in H as J. apply problem_to_sub_simpl_helper in J.
  rewrite J. simpl in H. auto.
Qed.


Lemma a_var_in_lTerm_not_In:forall(lt:lTerm),
  a_var_in_lTerm lt = None -> (forall v:var, ~ In (V v) lt).
Proof.
  intros. induction lt. auto. simpl in H.
  destruct a;firstorder;simpl; apply Classical_Prop.and_not_or;split;auto.
  - intro. inversion H1.
  - inversion H.
  - inversion H.
  - intro. inversion H1.
Qed.

Lemma problem_to_sub_simpl:forall(v:var)(sb:sub)(p:problem),
  problem_to_sub p = Some (v, sb) 
  -> problem_to_sub ([V v], (remove (V v) (Reducing_lr_Ord (lhs p ++ rhs p)))) = Some(v,sb).
Proof.
  intros. unfold problem_to_sub in H. destruct (a_var_in_lTerm (fst (rawP_to_reducedP p))) eqn:J.
  - apply a_var_in_lTerm_transform in J as J1. unfold problem_to_sub. 
    destruct (a_var_in_lTerm (fst (rawP_to_reducedP ([V v], remove (V v) (Reducing_lr_Ord (lhs p ++ rhs p))))))eqn:J2.
    + simpl in J2. inversion H. subst. clear H. rewrite J2 in J1. inversion J1.
      f_equal. f_equal. simpl. rewrite problem_to_sub_simpl_helper. auto.
      apply a_var_in_lTerm_In in J. now simpl in J.
    + simpl in J2. assert(K:=a_var_in_lTerm_not_In _ J2 v0).
      inversion H. rewrite H1 in *. apply a_var_in_lTerm_In in J1.
      apply K in J1. inversion J1.
  - inversion H.
Qed.


Lemma problem_solved_form:forall(v:var)(p:problem),
  solved_form [([V v], (remove (V v) (Reducing_lr_Ord (lhs p ++ rhs p))))].
Proof.
  intros. assert(Reduced_Ord (Reducing_lr_Ord (lhs p++rhs p))).
  apply Reducing_lr_Ord_Correct_Reduced_Ord. apply (remove_NReduced_Ord (V v)) in H.
  inversion H;subst. inversion H0;subst.

  repeat constructor;simpl;auto. 
  rewrite app_nil_r. clear H H0 H1 H2 H4. apply NReduced_NoDup in H3.
  unfold disjoint_In. intros. inversion H.
  - rewrite <- H0 in *. apply Not_In_Reduced_Ord_lTerm.
  - inversion H0.
Qed.


Definition Reduced_Problems(ps:problems):Prop:=
  Forall (fun p=> p = []) (map snd ps)
  /\
  Forall Reduced_Ord (map fst ps).

Lemma Reduced_Problems_rawPs_to_reducedPs:forall(ps:problems),
  Reduced_Problems (rawPs_to_reducedPs ps).
Proof.
  intros. unfold rawPs_to_reducedPs. unfold rawP_to_reducedP. 
  induction ps;constructor;simpl;auto.
  - apply Forall_cons. auto. inversion IHps. auto.
  - apply Forall_cons. apply Reducing_lr_Ord_Correct_Reduced_Ord. now inversion IHps.
Qed. 

Lemma Reduced_Problems_inv:forall(p:problem)(ps:problems),
  Reduced_Problems (p::ps) -> Reduced_Problems [p].
Proof.
  intros. inversion H. simpl in *. apply Forall_inv in H0. apply Forall_inv in H1.
  constructor;simpl. rewrite H0. auto. constructor;auto.
Qed.

Lemma Reduced_Problems_inv_tail:forall(p:problem)(ps:problems),
  Reduced_Problems (p::ps) -> Reduced_Problems ps.
Proof.
  intros. inversion H. simpl in *. apply Forall_inv_tail in H0. apply Forall_inv_tail in H1.
  constructor;auto.
Qed.

Lemma steps_simpl_Reduced_Problems:forall(sys:problems_set),
  Reduced_Problems (fst sys) -> Reduced_Problems (fst (step sys)).
Proof.
  intros. inversion H. constructor.
  - clear H1. destruct sys. simpl. destruct p. auto.
    destruct (lTerm_eqv_bool (fst p) []). simpl in *. now apply Forall_inv_tail in H0.
    destruct (problem_to_sub p). 
    + destruct p2. simpl in *. apply Forall_inv_tail in H0. clear H.
      induction p1. auto. simpl in H0. simpl. apply Forall_cons. 
      unfold rhs. apply Forall_inv in H0. rewrite H0. auto.
      apply Forall_inv_tail in H0. auto.
    + auto.
  - clear H0. destruct sys. simpl in *. destruct p. auto.
    destruct (lTerm_eqv_bool (fst p) []). simpl in *. now apply Forall_inv_tail in H1.
    destruct (problem_to_sub p). 
    + destruct p2. simpl in *. umap_fst_comm. clear H H1.
      induction ((map (lftl s) (map fst p1))). simpl. auto.
      simpl. apply Forall_cons. apply Reducing_lr_Ord_Correct_Reduced_Ord.
      auto.
    + simpl. auto.
Qed.



Lemma steps_n_simpl_Reduced_Problems:forall(n:nat)(sys:problems_set),
  Reduced_Problems (fst sys) -> Reduced_Problems (fst (steps n sys)).
Proof.
  intros. induction n. simpl. auto. rewrite <- steps_step_plus1_left.
  apply steps_simpl_Reduced_Problems. auto.
Qed.




Lemma steps_simpl_solves_fst:forall(sys:problems_set)(sb:sub),
  solves_problems sb (fst sys) -> solves_problems sb (snd sys)
  -> solves_problems sb (fst (step sys)).
Proof.
  intros.  
  - destruct sys. simpl in *. destruct p. 
    + auto.
    + destruct (lTerm_eqv_bool (fst p) []). simpl. apply solves_problems_cons in H. now destruct H.
      destruct (problem_to_sub p) eqn:J.
      -- destruct p2. simpl. apply solves_problems_cons in H. destruct H.
         apply problem_to_sub_simpl in J as J1.
         assert(J2:=problem_solved_form v p).
         assert(J3:=unifiers_preserve_singleton sb p v). unfold problem_to_sub in J.
         destruct (a_var_in_lTerm (fst (rawP_to_reducedP p))) eqn: J4.
         ++ inversion J.
            assert(J5:=unifiers_preserve_singleton sb p v0 J4 H). rewrite H3 in *.
            assert(L:=solved_form_unifiers_equal v sb s _ J2 J5 J1).
            clear J J2 J3 J4 H3 J5. symmetry in H4. rewrite <- H4.
            assert(forall v' : var, sb v' == compose_sub sb s v' ).
            intros. now apply eqv_sym.
            assert(K:=sub_v_eqv_solves_problems _ _ p1 H2).
            apply solves_problems_solves_Rproblems.
            apply compose_solves_apply_sub_simple. auto.
         ++ inversion J.
      -- auto.
Qed.

Lemma steps_simpl_solves_snd:forall(sys:problems_set)(sb:sub),
  solves_problems sb (fst sys) -> solves_problems sb (snd sys) -> Reduced_Problems (fst sys)
  -> solves_problems sb (snd (step sys)).
Proof.
  intros. 
  destruct sys. simpl in *. destruct p.
  - auto.
  - destruct (lTerm_eqv_bool (fst p) []). auto.
    destruct (problem_to_sub p) eqn:J. 
    + destruct p2. simpl in *. apply solves_problems_cons. split.
      -- apply Reduced_Problems_inv in H1. inversion H1.
         simpl in *. apply Forall_inv in H2. apply Forall_inv in H3.
         apply solves_problems_cons in H. destruct H. unfold problem_to_sub in J.
         destruct (a_var_in_lTerm (fst (rawP_to_reducedP p))) eqn:J2. inversion J. subst.
         clear J. assert(J1:=unifiers_preserve_singleton sb p v J2 H).
         unfold rhs in *. rewrite H2 in J1. rewrite app_nil_r in J1. unfold lhs in J1.
         apply Reduced_Ord_Reducing_lr_Ord in H3. rewrite H3 in J1. auto.
         inversion J.
      -- apply solves_problems_solves_Rproblems. apply compose_solves_apply_sub_simple.
         apply problem_to_sub_simpl in J as J1. 
         assert(J2:=problem_solved_form v p). unfold problem_to_sub in J. 
         destruct (a_var_in_lTerm (fst (rawP_to_reducedP p))) eqn: J4.
         ++ inversion J. apply solves_problems_cons in H. destruct H.
            assert(J5:=unifiers_preserve_singleton sb p v0 J4 H). rewrite H3 in *.
            assert(L:=solved_form_unifiers_equal v sb s _ J2 J5 J1).
            clear J J2 J1 J4 H3 J5. symmetry in H4. rewrite <- H4.
            assert(forall v' : var, sb v' == compose_sub sb s v' ).
            intros. now apply eqv_sym.
            assert(K:=sub_v_eqv_solves_problems _ _ p0 H3). auto.
         ++ inversion J.
    + auto.
Qed.


Lemma steps_simpl_solves_fst_snd:forall(sys:problems_set)(sb:sub),
  solves_problems sb (fst sys) -> solves_problems sb (snd sys) -> Reduced_Problems (fst sys)
  ->
  solves_problems sb (fst (step sys)) /\ solves_problems sb (snd (step sys)).
Proof.
  intros. assert(H2:=steps_simpl_solves_snd sys sb H H0 H1).
  assert(H3:=steps_simpl_solves_fst sys sb H H0). now split.
Qed.


Lemma steps_n_simpl_solves_fst_snd:forall(n:nat)(sys:problems_set)(sb:sub),
  Reduced_Problems (fst sys) -> solves_problems sb (fst sys) -> solves_problems sb (snd sys)
  ->
  solves_problems sb (fst (steps n sys)) /\ solves_problems sb (snd (steps n sys)).
Proof.
  intros. induction n. auto.
  destruct IHn. rewrite <- steps_step_plus1_left. apply steps_simpl_solves_fst_snd;
  auto. apply steps_n_simpl_Reduced_Problems. auto.
Qed.


Lemma steps_sub_preserve_ps1:forall(ps:problems)(ps1 ps2:problems)(sb:sub),
  steps (measure (problems_set_ready ps)) (problems_set_ready ps) = (ps1,ps2) 
  -> solves_problems sb ps -> solves_problems sb ps1.
Proof.
  intros. 
  assert(solves_problems sb (fst (problems_set_ready ps)) 
  /\ solves_problems sb (snd (problems_set_ready ps))
  /\ Reduced_Problems (fst (problems_set_ready ps))); unfold problems_set_ready;simpl. 
  {split. assert(J:=rawPs_to_reducedPs_sub_preserve ps sb). auto. split. now ufps. 
  apply Reduced_Problems_rawPs_to_reducedPs. } destruct H1. destruct H2.
  assert(K:=steps_n_simpl_solves_fst_snd (measure (problems_set_ready ps)) 
  (problems_set_ready ps) sb H3 H1 H2). destruct K. rewrite H in H4. simpl in H4. auto.
Qed.


Lemma steps_sub_preserve_ps1_forall:forall(ps:problems)(ps1 ps2:problems),
  steps (measure (problems_set_ready ps)) (problems_set_ready ps) = (ps1,ps2) 
  -> (forall sb:sub, solves_problems sb ps -> solves_problems sb ps1).
Proof. 
  intros. assert(L:=steps_sub_preserve_ps1 _ _ _ sb H). auto.
Qed.


(*
Important theorem about substitution solves original problem solves the problmes after transformation
*)
Theorem steps_sub_preserve_ps2:forall(ps:problems)(ps1 ps2:problems)(sb:sub),
  steps (measure (problems_set_ready ps)) (problems_set_ready ps) = (ps1,ps2) 
  -> solves_problems sb ps -> solves_problems sb ps2.
Proof.
  intros. 
  assert(solves_problems sb (fst (problems_set_ready ps)) 
  /\ solves_problems sb (snd (problems_set_ready ps))
  /\ Reduced_Problems (fst (problems_set_ready ps))); unfold problems_set_ready;simpl. 
  {split. assert(J:=rawPs_to_reducedPs_sub_preserve ps sb). auto. split. now ufps. 
  apply Reduced_Problems_rawPs_to_reducedPs. } destruct H1. destruct H2.
  assert(K:=steps_n_simpl_solves_fst_snd (measure (problems_set_ready ps)) 
  (problems_set_ready ps) sb H3 H1 H2). destruct K. rewrite H in H5. simpl in H5. auto.
Qed.

(*
Important theorem about substitution solves original problem solves the problmes after transformation
*)
Theorem steps_sub_preserve_ps2_forall:forall(ps:problems)(ps1 ps2:problems),
  steps (measure (problems_set_ready ps)) (problems_set_ready ps) = (ps1,ps2) 
  -> (forall sb:sub, solves_problems sb ps -> solves_problems sb ps2).
Proof.
  intros. assert(L:=steps_sub_preserve_ps2 _ _ _ sb H). auto.
Qed.








(* ============================================================================= *)

Lemma unifiers_preserve_singleton_back:forall(sb:sub)(p:problem)(v:var),
  a_var_in_lTerm (fst (rawP_to_reducedP p)) = Some v ->
  solves_problem sb ([V v], (remove (V v) (Reducing_lr_Ord (lhs p ++ rhs p)))) ->
  solves_problem sb p.
Proof.
  intros. destruct p. ufp. apply lTerm_eqv_lTerm_eqv_nil in H0. 
  apply lTerm_eqv_same_side_nil. assert([lft sb (V v)] ++
  map (lft sb) (remove (V v) (Reducing_lr_Ord (l ++ l0))) =
  lftl sb (V v :: (remove (V v) (Reducing_lr_Ord (l ++ l0))))).
  simpl. auto. unfold lftl in *. rewrite H1 in H0. clear H1. apply lr_sym.
  apply lr_trans with (map (lft sb) (V v :: remove (V v) (Reducing_lr_Ord (l ++ l0)))).
  apply lr_sym. auto. rewrite <- map_app. 
  assert(J:=lTerm_eqv_lftl). unfold lftl in *.
  apply J. clear J H0. assert(J:=Reducing_lr_Ord_Correct_eqv (l ++ l0)).
  apply lr_sym in J. assert(Reducing_lr_Ord (l ++ l0) =l= V v :: remove (V v) (Reducing_lr_Ord (l ++ l0))).
  {apply lr_perm. apply a_var_in_lTerm_In in H. apply Permutation_In_cons_remove. auto. }
  apply lr_sym in H0. assert(L:=lr_trans _ _ (l++l0) H0). auto.
Qed.


Lemma p_empty_all_solves:forall(sb:sub)(p:problem),
  Reduced_Problems [p] ->
  lTerm_eqv_bool (fst p) [] = true -> solves_problem sb p.
Proof.
  intros. inversion H. simpl in *. ufp. apply Forall_inv in H1. apply Forall_inv in H2.
  unfold rhs. rewrite H1 in *. apply lTerm_eqv_bool_correct in H0.
  unfold lhs. apply lTerm_eqv_Reduced_nil in H0. rewrite app_nil_r in H0.
  apply Reduced_Ord_Reducing_lr_Ord in H2. rewrite H2 in H0. rewrite H0. apply lr_relf.
Qed.


Lemma steps_simpl_solves_fst_back:forall(sys:problems_set)(sb:sub),
  Reduced_Problems (fst sys) ->
  solves_problems sb (fst (step sys)) -> solves_problems sb (snd (step sys)) 
  ->
  solves_problems sb (fst sys).
Proof.
  intros sys sb KK. intros. destruct sys. simpl in *. destruct p. 
  - auto.
  - destruct (lTerm_eqv_bool (fst p) []) eqn:JJ. simpl in *. inversion KK. simpl in *.
    apply Reduced_Problems_inv in KK.
    assert(JJJ:=p_empty_all_solves sb p KK JJ). apply solves_problems_cons. split; auto.
    destruct (problem_to_sub p) eqn:J.
    -- destruct p2. simpl. apply solves_problems_cons. simpl in *. split.
        + apply problem_to_sub_simpl in J as J1.
          assert(J2:=problem_solved_form v p).
          unfold problem_to_sub in J.
          destruct (a_var_in_lTerm (fst (rawP_to_reducedP p))) eqn: J4.
          ++ inversion J. rewrite H2 in *. 
             assert(J5:=unifiers_preserve_singleton_back sb p v J4 ). apply J5.
             clear J5 J H2. symmetry in H3.  
             apply solves_problems_cons in H0. destruct H0.
             
             assert(Reduced_Problems [p]). { now apply Reduced_Problems_inv in KK. }
             destruct H2. simpl in *. apply Forall_inv in H2. apply Forall_inv in H4.
             unfold rhs in *. unfold lhs in *.
             rewrite H2 in *. rewrite app_nil_r in *.
             apply Reduced_Ord_Reducing_lr_Ord in H4. rewrite H4 in *. auto.
          ++ inversion J.
        + apply solves_Rproblems_solves_problems in H.
          apply solves_apply_sub_compose_simple in H.
          apply solves_problems_cons in H0. destruct H0. clear H1.
          apply problem_to_sub_simpl in J as J1.
          assert(J2:=problem_solved_form v p).
          unfold problem_to_sub in J.
          destruct (a_var_in_lTerm (fst (rawP_to_reducedP p))) eqn: J4.
          ++ inversion J. rewrite H2 in *. clear H2 J. 
             symmetry in H3. 
             
             assert(Reduced_Problems [p]). { now apply Reduced_Problems_inv in KK. } assert(L:=H1).
             destruct H1. simpl in *. apply Forall_inv in H2. apply Forall_inv in H1.
             unfold rhs in *. unfold lhs in *.
             rewrite H1 in *. rewrite app_nil_r in *.
             apply Reduced_Ord_Reducing_lr_Ord in H2. rewrite H2 in *. 
             assert(J:=solved_form_unifiers_equal v sb s _ J2 H0 J1).
             assert(J3:=sub_v_eqv_solves_problems _ _ p1 J). auto.
          ++ inversion J.
    -- auto.
Qed.

Lemma steps_simpl_solves_snd_back:forall(sys:problems_set)(sb:sub),
  Reduced_Problems (fst sys) ->
  solves_problems sb (fst (step sys)) -> solves_problems sb (snd (step sys)) 
  ->
  solves_problems sb (snd sys).
Proof.
  intros sys sb KK. intros. destruct sys. simpl in *. destruct p.
  - auto.
  - destruct (lTerm_eqv_bool (fst p) []). simpl in *;auto.
    destruct (problem_to_sub p) eqn:J. 
    + destruct p2. simpl in *. apply solves_problems_cons in H0.
      destruct H0. apply solves_Rproblems_solves_problems in H1. 
      apply problem_to_sub_simpl in J as J1.
      assert(J2:=problem_solved_form v p).
      unfold problem_to_sub in J.
      destruct (a_var_in_lTerm (fst (rawP_to_reducedP p))) eqn: J4.
      ++ inversion J. rewrite H3 in *. assert(KK1:=KK). destruct KK1.
         apply Forall_inv in H2. apply Forall_inv in H5. 
         assert(J5:=unifiers_preserve_singleton_back sb p v J4 ). 
         unfold rhs in *. unfold lhs in *. rewrite H2 in *. rewrite app_nil_r in *.
         apply Reduced_Ord_Reducing_lr_Ord in H5. rewrite H5 in *.
         assert(K:=solved_form_unifiers_equal v sb s _ J2 H0 J1). 
         apply solves_apply_sub_compose_simple in H1. 
         assert(J3:=sub_v_eqv_solves_problems _ _ p0 K). auto.
      ++ inversion J.
    + auto.
Qed. 

Lemma steps_simpl_solves_fst_snd_back:forall(sys:problems_set)(sb:sub),
  Reduced_Problems (fst sys) ->
  solves_problems sb (fst (step sys)) -> solves_problems sb (snd (step sys)) 
  ->
  solves_problems sb (fst sys) /\ solves_problems sb (snd sys).
Proof.
  intros. 
  assert(K:= steps_simpl_solves_fst_back _ _ H H0 H1).
  assert(K1:= steps_simpl_solves_snd_back _ _ H H0 H1).
  now split.
Qed.


Lemma steps_n_simpl_solves_fst_snd_back:forall(n:nat)(sys:problems_set)(sb:sub),
  Reduced_Problems (fst sys) ->
  solves_problems sb (fst (steps n sys)) -> solves_problems sb (snd (steps n sys))
  ->
  solves_problems sb (fst sys) /\ solves_problems sb (snd sys).
Proof.
  intros. induction n. auto. rewrite <- steps_step_plus1_left in H0.
  rewrite <- steps_step_plus1_left in H1. 
  assert(K1:=steps_n_simpl_Reduced_Problems n _ H).
  assert(K:= steps_simpl_solves_fst_snd_back _ _ K1 H0 H1). destruct K. auto.
Qed.


(*
Important theorem about substitution solves the problmes after transformation solves original problem
IF the algorithm halt at right states
*)

Theorem steps_sub_preserve_ps2_rev:forall(ps:problems)(ps1 ps2:problems)(sb:sub),
  steps (measure (problems_set_ready ps)) (problems_set_ready ps) = (ps1,ps2) ->
  ps1 = [] -> solves_problems sb ps2 -> solves_problems sb ps.
Proof.
  intros.
  assert(Reduced_Problems (fst (problems_set_ready ps))).
  unfold problems_set_ready. simpl. apply Reduced_Problems_rawPs_to_reducedPs.
  assert(L:=steps_n_simpl_solves_fst_snd_back (measure (problems_set_ready ps))
  ((problems_set_ready ps)) sb H2). rewrite H in L. simpl in L.
  assert(solves_problems sb ps1 /\ solves_problems sb ps2).
  split.
  - rewrite H0. now ufps.
  - auto.
  - destruct H3. assert(L1:=L H3 H4). destruct L1.
  apply reducedPs_to_rawPs_sub_preserve. auto.
Qed.

(*
Important theorem about mgu preserve
*)
Theorem steps_mgu_preserve:forall(ps:problems)(ps1 ps2:problems)(sb:sub),
  steps (measure (problems_set_ready ps)) (problems_set_ready ps) = (ps1,ps2) ->
  ps1 = [] -> mgu_xor sb ps2 -> mgu_xor sb ps.
Proof.
  intros. unfold mgu_xor in *.
  intros.
  assert(L:=steps_sub_preserve_ps2 _ _ _ sb1 H).
  assert(L1:=steps_sub_preserve_ps2_rev _ _ _ sb1 H H0).
  auto.
Qed. 


Definition rawPs_to_solvedPs(ps:problems):option problems:=
  match steps (measure((rawPs_to_reducedPs ps),[])) ((rawPs_to_reducedPs ps),[]) with
  |(nil,ps) => Some ps
  |(_,_) => None
  end.
  
Definition XORUnification(ps:problems) : option sub:=
  match (rawPs_to_solvedPs ps) with
  |Some ps' => Some (solved_form_to_sub ps')
  |None => None
  end.

Lemma steps_solves_preserve:forall(ps:problems)(ps1 ps2:problems)(sb:sub)(n:nat),
  steps n (problems_set_ready ps) = (ps1,ps2) ->
  solves_problems sb ps -> solves_problems sb ps1 /\ solves_problems sb ps2.
Proof.
  intros. 
  assert(solves_problems sb (fst (problems_set_ready ps)) 
  /\ solves_problems sb (snd (problems_set_ready ps))
  /\ Reduced_Problems (fst (problems_set_ready ps))); unfold problems_set_ready;simpl. 
  {split. assert(J:=rawPs_to_reducedPs_sub_preserve ps sb). auto. split. now ufps.
  apply Reduced_Problems_rawPs_to_reducedPs. } destruct H1. destruct H2.
  assert(K:=steps_n_simpl_solves_fst_snd n 
  (problems_set_ready ps) sb H3 H1 H2). destruct K. rewrite H in H5. simpl in H5. 
  rewrite H in H4. simpl in H4. auto.
Qed.


Lemma steps_sub_not_empty_not_solvable:forall(ps ps1 ps2:problems)(p:problem),
  steps (measure (problems_set_ready ps)) (problems_set_ready ps) = (p::ps1,ps2) ->
  fixed_pss (p::ps1,ps2).
Proof.
  intros. assert(J:=steps_fixed_sys (problems_set_ready ps)). rewrite H in J. auto.
Qed.


Lemma fixed_p_not_empty:forall(ps1 ps2:problems)(p:problem),
  Reduced_Problems (p::ps1) ->
  fixed_pss (p::ps1,ps2) -> p_solvable_bool p = false.
Proof.
  intros. unfold rd_eqv_bool. destruct (lTerm_eqv_bool (fst p) []) eqn:J;auto.
  exfalso.
  apply lTerm_eqv_bool_correct in J. unfold rawP_to_reducedP in J. inversion H.
  apply Forall_inv in H1. apply Forall_inv in H2.  
  apply Reduced_Ord_Reducing_lr_Ord in H2. 
  apply lTerm_eqv_Reduced_nil in J. rewrite app_nil_r in J. rewrite H2 in J.
  unfold fixed_pss in H0. unfold step in H0. rewrite J in H0. simpl in H0. inversion H0. 
  apply list_lenght_correct in H4. simpl in H4. lia. unfold p_solvable_bool.
  unfold lTerm_solvable_bool. inversion H. apply Forall_inv in H1. apply Forall_inv in H2. 
  apply orb_false_iff. split.
  - simpl. unfold lhs. unfold rhs. rewrite H1. rewrite app_nil_r. apply Reduced_Ord_Reducing_lr_Ord in H2.
    rewrite H2. unfold rd_eqv_bool. auto.
  - unfold rawP_to_reducedP. unfold lhs. unfold rhs. rewrite H1. rewrite app_nil_r. apply Reduced_Ord_Reducing_lr_Ord in H2.
    rewrite H2. simpl. unfold fixed_pss in H0. unfold step in H0. 
    destruct (lTerm_eqv_bool (fst p) []).
    + inversion H0. apply list_lenght_correct in H4. simpl in H4. lia.
    + destruct (problem_to_sub p) eqn:J1. 
      -- unfold problem_to_sub in J1. destruct (a_var_in_lTerm (fst (rawP_to_reducedP p))).
         inversion J1. subst. clear J1 J H1 H2. inversion H0. clear H0 H3.
         apply list_lenght_correct in H2. unfold Rproblems in H2. rewrite <- map_same_length in H2.
         unfold apply_sub_problems in H2. rewrite <- map_same_length in H2. simpl in H2. lia.         
         inversion J1.
      -- unfold problem_to_sub in J1. destruct (a_var_in_lTerm (fst (rawP_to_reducedP p))) eqn:JJ.
         inversion J1. unfold rawP_to_reducedP in JJ. unfold lhs in *. unfold rhs in *.
         rewrite H1 in JJ. rewrite app_nil_r in JJ. 
         rewrite H2 in JJ. simpl in JJ. clear H J1 H0 J H1 H2. induction (fst p). auto.
         simpl. destruct a;auto. inversion JJ.
Qed.

Definition not_solvable_problems(ps:problems):Prop:=
  forall sb:sub, ~ solves_problems sb ps.


Lemma one_not_solvable_problems:forall(ps:problems)(p:problem),
  p_solvable_bool p = false -> In p ps -> not_solvable_problems ps.
Proof.
  intros. induction ps. inversion H0.
  simpl in H0. destruct H0.
  - rewrite H0. unfold not_solvable_problems. intros. intro. apply solves_problems_cons in H1.
    destruct H1. apply p_solvable_bool_false_complete in H. unfold not_solvable_problem in H.
    assert(H3:=H sb). auto. 
  - apply IHps in H0. unfold not_solvable_problems. intros. intro.
    apply solves_problems_cons in H1. destruct H1. unfold not_solvable_problems in H0.
    assert(H3:=H0 sb). auto.
Qed.


Theorem fixed_not_solvable:forall(ps1 ps2:problems)(p:problem),
  Reduced_Problems (p::ps1) ->
  fixed_pss (p::ps1,ps2) -> not_solvable_problems (p::ps1).
Proof.
  intros. assert(L:=fixed_p_not_empty _ _ _ H H0).
  assert(In p (p::ps1)). now left.
  assert(L1:=one_not_solvable_problems _ _ L H1). auto.
Qed.

(*
Important theorem about not solvablility preserve
*)
Theorem same_unifiers_both_not_solvable:forall(ps1 ps2:problems),
  (forall sb':sub, solves_problems sb' ps2 -> solves_problems sb' ps1) ->
  not_solvable_problems ps1 -> not_solvable_problems ps2.
Proof. 
  intros. unfold not_solvable_problems in *. 
  intros. intro. apply H in H1. apply H0 in H1. auto.
Qed.

