(* 

This file Connect all the proof together from the most top level.

If a problems is solvable, then the algorithm returns idempotent mgu.
If a problems is not solvable, then the algorithm returns None.

*)

From XORUnif Require Export Unification.


Definition XORUnification(ps:problems) : option sub:=
  match (rawPs_to_solvedPs ps) with
  |Some ps' => Some (solved_form_to_sub ps')
  |None => None
  end.


(*
Algo returns none means not solvable
*)
Theorem XORUnification_not_solvable:forall(ps:problems),
  XORUnification ps = None -> not_solvable_problems ps.
Proof.
  intros. unfold XORUnification in H. destruct(rawPs_to_solvedPs ps) eqn:J.
  - inversion H.
  - clear H.  
    unfold rawPs_to_solvedPs in J. 
    destruct (steps (measure (rawPs_to_reducedPs ps, [])) (rawPs_to_reducedPs ps, [])) eqn:J1.
    destruct p. inversion J. clear J.
    apply steps_sub_not_empty_not_solvable in J1 as J2.
    assert(J3:=Reduced_Problems_rawPs_to_reducedPs ps).
    assert(J4:=steps_n_simpl_Reduced_Problems (measure (rawPs_to_reducedPs ps, [])) (rawPs_to_reducedPs ps, [])).
    simpl in J4. apply J4 in J3. clear J4. rewrite J1 in J3. simpl in J3.
    assert(J4:=fixed_not_solvable _ _ _ J3 J2).
    assert(J5:=steps_sub_preserve_ps1_forall _ _ _ J1).
    assert(J6:=same_unifiers_both_not_solvable _ _ J5). auto.
Qed.

(*
Algo returns a sub means this sub solves the problem
*)
Theorem XORUnification_solves:forall(ps:problems)(sb:sub),
  XORUnification ps = Some sb -> solves_problems sb ps.
Proof.
  intros. unfold XORUnification in H. destruct (rawPs_to_solvedPs ps) eqn:H1.
  - unfold rawPs_to_solvedPs in H1. 
    destruct (steps (measure (rawPs_to_reducedPs ps, [])) (rawPs_to_reducedPs ps, [])) eqn:H2.
    destruct p0. 
    + inversion H1. inversion H. assert(L3:=rawPs_to_solvedPs_solved_form _ _ _ H2).
      assert(L2:=solved_form_sub_solves p1 L3).
      assert(L1:= steps_sub_preserve_ps2_rev _ _ _ (solved_form_to_sub p) H2). rewrite H3 in *.
      apply L1;auto.
    + inversion H1.
  - inversion H.
Qed. 

(*
Algo returns a sub means this sub is the mgu of the problem
*)
Theorem XORUnification_mgu:forall(ps:problems)(sb:sub),
  XORUnification ps = Some sb -> mgu_xor sb ps.
Proof.
  intros. unfold XORUnification in H. destruct (rawPs_to_solvedPs ps) eqn:H1.
  - unfold rawPs_to_solvedPs in H1. 
    destruct (steps (measure (rawPs_to_reducedPs ps, [])) (rawPs_to_reducedPs ps, [])) eqn:H2.
    destruct p0. 
    + inversion H1. inversion H. assert(L3:=rawPs_to_solvedPs_solved_form _ _ _ H2).
      assert(L2:= solved_form_sub_mgu p1 L3). 
      assert(L4:=steps_mgu_preserve _ _ _ (solved_form_to_sub p) H2).
      apply L4;auto. now rewrite H3 in *.
    + inversion H1.
  - inversion H.
Qed. 

(*
Algo returns a sub means this sub is idempotent
*)
Theorem XORUnification_idpt:forall(ps:problems)(sb:sub),
  XORUnification ps = Some sb -> idempotent sb.
Proof.
  intros. unfold XORUnification in H. destruct (rawPs_to_solvedPs ps) eqn:H1.
  - unfold rawPs_to_solvedPs in H1. 
    destruct (steps (measure (rawPs_to_reducedPs ps, [])) (rawPs_to_reducedPs ps, [])) eqn:H2.
    destruct p0. 
    + inversion H1. inversion H. assert(L3:=rawPs_to_solvedPs_solved_form _ _ _ H2).
      assert(L2:= solved_form_sub_idpt p1 L3). now rewrite H3 in *.
    + inversion H1.
  - inversion H.
Qed. 

Definition problems_unifiable(ps:problems):Prop:=
  exists sb:sub, solves_problems sb ps.
  

(*
Backwards, if a problem is solvable, the algo will returns a sub
*)
Theorem unifiable_return_sub:forall(ps:problems),
  problems_unifiable ps -> (exists sb:sub, XORUnification ps = Some sb).
Proof.
  intros. destruct (XORUnification ps)eqn:J.
  - exists s. auto.
  - unfold problems_unifiable in H.
    apply XORUnification_not_solvable in J. unfold not_solvable_problems in J. destruct H. exfalso.
    apply (J x). auto.
Qed.

(*
Backwards, if a problem is not solvable, the algo will returns none
*)
Theorem not_unifiable_return_None:forall(ps:problems),
  ~(problems_unifiable ps) -> XORUnification ps = None.
Proof.
  intros. destruct (XORUnification ps)eqn:J.
  - exfalso. apply H. unfold problems_unifiable. exists s. apply XORUnification_solves. auto.
  - auto.
Qed.




(*
The above proof is all about lTerm
This is a connection to term level
*)
Definition problem_orig:= prod term term.
Definition problems_orig:= list problem_orig.

Definition problem_orig_to_problem(po:problem_orig):problem:=
  ((term_to_lTerm (fst po)),(term_to_lTerm (snd po))).

Definition problems_orig_to_problems(pso:problems_orig):problems:=
  map problem_orig_to_problem pso.


Definition equal_problem_orig(p:problem_orig):Prop:=
  fst p == snd p.

Definition apply_sub_problem_orig (sb:sub)(p:problem_orig):problem_orig:=
  (lft sb (fst p), lft sb (snd p)).

Definition solves_problem_orig(sb:sub)(po:problem_orig):Prop:=
  equal_problem_orig (apply_sub_problem_orig sb po).

Definition apply_sub_problems_orig (sb:sub)(pos:problems_orig):problems_orig:=
  map (apply_sub_problem_orig sb) pos.

Definition equal_problems_orig(pos:problems_orig):Prop:=
  Forall equal_problem_orig pos.

Definition solves_problems_orig (sb:sub)(pos:problems_orig):Prop:=
  equal_problems_orig (apply_sub_problems_orig sb pos).

Definition XORUnification_orig(pso:problems_orig):option sub:=
  XORUnification (problems_orig_to_problems pso).


Definition mgu_xor_orig(sb:sub)(pos:problems_orig):Prop:=
  forall (sb1:sub), solves_problems_orig sb1 pos ->
  leq_sub_xor sb sb1.

Definition not_solvable_problems_orig(ps:problems_orig):Prop:=
  forall sb:sub, ~ solves_problems_orig sb ps.

Ltac ufpo:= unfold solves_problem_orig in *; unfold equal_problem_orig in *;
unfold apply_sub_problem_orig in *; simpl in *.

Ltac ufpos:= unfold solves_problems_orig in *; unfold equal_problems_orig in *;
unfold equal_problem_orig in *;
unfold apply_sub_problems_orig in *; simpl in *.

(*
If the algo returns a None, the the problem is not solvable
*)
Lemma XORUnification_not_solvable_orig:forall(ps:problems_orig),
  XORUnification_orig ps = None -> not_solvable_problems_orig ps.
Proof.
  intros. unfold XORUnification_orig in H. unfold not_solvable_problems_orig.
  apply XORUnification_not_solvable in H. unfold not_solvable_problems in H.
  intros. intro. apply (H sb). clear H.
  induction ps.
  - ufps. auto. 
  - ufps. ufpos.
    apply Forall_cons.
    + apply Forall_inv in H0. ufpos.
      assert(H1:=lft_lftl_correct sb (fst a)).
      assert(H2:=lft_lftl_correct sb (snd a)).
      assert(H3:=lr_trans (lftl sb (term_to_lTerm (fst a))) (term_to_lTerm (lft sb (fst a)))
      (lftl sb (term_to_lTerm (snd a)))). apply H3.
      -- apply lr_sym. apply lft_lftl_correct.
      -- clear H3. apply lr_sym. apply lr_sym in H2.
         assert(H3:=lr_trans 
               (lftl sb (term_to_lTerm (snd a))) 
               (term_to_lTerm (lft sb (snd a)))
               (term_to_lTerm (lft sb (fst a)))). 
          apply H3. apply lr_sym. apply lft_lftl_correct.
          clear H2 H1 H3. apply lr_sym.
          apply lTerm_eqv_Sound. auto.
    + apply IHps. now apply Forall_inv_tail in H0.
Qed.

(*
If the algo returns a sub, then the sub solves the problem
*)
Lemma XORUnification_orig_solves:forall(pso:problems_orig)(sb:sub),
  XORUnification_orig pso = Some sb -> solves_problems_orig sb pso.
Proof.
  intros. unfold XORUnification_orig in H.
  apply XORUnification_solves in H. ufpos. ufps. induction pso.
  - simpl. auto.
  - apply Forall_cons.
    + apply Forall_inv in H. clear IHpso. unfold problem_orig_to_problem in H.
      unfold lhs in *. unfold rhs in *. simpl in *. 
      assert(H1:=lft_lftl_correct sb (fst a)).
      assert(H2:=lft_lftl_correct sb (snd a)).
      assert(H3:=lr_trans _ _ _ H1 H). apply lr_sym in H2.
      assert(H4:=lr_trans _ _ _ H3 H2). 
      apply lTerm_eqv_Complete. auto.
    + apply IHpso. now apply Forall_inv_tail in H.
Qed.
  

(*
If the algo returns a sub, then the sub is the mgu of the problem
*)
Lemma XORUnification_mgu_orig:forall(pos:problems_orig)(sb:sub),
  XORUnification_orig pos = Some sb -> mgu_xor_orig sb pos.
Proof.
  intros. unfold XORUnification_orig in H. 
  apply XORUnification_mgu in H. unfold mgu_xor in H.
  unfold mgu_xor_orig. intros.
  assert(H1:=H sb1). clear H. apply H1. clear H1.
  induction pos.
  - ufps. auto. 
  - ufps. ufpos.
    apply Forall_cons.
    + apply Forall_inv in H0. ufpos.
      assert(H1:=lft_lftl_correct sb1 (fst a)).
      assert(H2:=lft_lftl_correct sb1 (snd a)).
      assert(H3:=lr_trans (lftl sb1 (term_to_lTerm (fst a))) (term_to_lTerm (lft sb1 (fst a)))
      (lftl sb1 (term_to_lTerm (snd a)))). apply H3.
      -- apply lr_sym. apply lft_lftl_correct.
      -- clear H3. apply lr_sym. apply lr_sym in H2.
         assert(H3:=lr_trans 
               (lftl sb1 (term_to_lTerm (snd a))) 
               (term_to_lTerm (lft sb1 (snd a)))
               (term_to_lTerm (lft sb1 (fst a)))). 
          apply H3. apply lr_sym. apply lft_lftl_correct.
          clear H2 H1 H3. apply lr_sym. apply lTerm_eqv_Sound. auto.
    + apply IHpos. now apply Forall_inv_tail in H0.
Qed. 

(*
If the algo returns a sub, then the sub is idempotent
*)
Lemma XORUnification_idpt_orig:forall(ps:problems_orig)(sb:sub),
  XORUnification_orig ps = Some sb -> idempotent sb.
Proof.
  intros. unfold XORUnification_orig in H. apply XORUnification_idpt in H. auto.
Qed. 


Definition problems_unifiable_orig(ps:problems_orig):Prop:=
  exists sb:sub, solves_problems_orig sb ps.
  
(*
Backwards, if the problem is unifiable, then the algo returns a sub
*)
Lemma unifiable_return_sub_orig:forall(ps:problems_orig),
  problems_unifiable_orig ps -> (exists sb:sub, XORUnification_orig ps = Some sb).
Proof.
  intros. destruct (XORUnification_orig ps)eqn:J.
  - exists s. auto.
  - unfold problems_unifiable_orig in H.
    apply XORUnification_not_solvable_orig in J. unfold not_solvable_problems_orig in J. 
    destruct H. exfalso.
    apply (J x). auto.
Qed.

(*
Backwards, if the problem is not unifiable, then the algo returns a none
*)
Lemma not_unifiable_return_None_orig:forall(ps:problems_orig),
  ~ (problems_unifiable_orig ps) -> XORUnification_orig ps = None.
Proof.
  intros. destruct (XORUnification_orig ps) eqn:J.
  - exfalso. apply H. unfold problems_unifiable_orig. exists s. apply XORUnification_orig_solves. auto.
  - auto.
Qed.