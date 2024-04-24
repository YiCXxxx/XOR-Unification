(*
This file mainly stores some useful Lemma for Permutations
*)

From XORUnif Require Export TheoryDef.
From Coq Require Export Permutation.

Fixpoint remove (t:term)(tl:list term): list term :=
  match tl with
  |[] => []
  |t'::tl' => if term_beq_syn t' t 
                then tl' 
                else t' ::(remove t tl')
  end.


Theorem Permutation_In {X:Type}: forall (l l': list X) (t:X),
  Permutation l l'-> In t l -> In t l'.
Proof.
  intros. induction H. inversion H0. inversion H0. rewrite H1.
  now left. firstorder. inversion H0. right; now left. inversion H.
  now left. right;now right. firstorder.
Qed.

Lemma Not_In_False {X:Type}: forall (l: list X) (t:X),
  ~ In t (t::l) -> False.
Proof.
  intros. apply not_in_cons in H. destruct H. now apply H.
Qed.

Theorem Permutation_Not_In {X:Type}: forall (l l': list X) (t:X),
  Permutation l l'-> ~ In t l -> ~ In t l'.
Proof.
  intros. induction H;simpl;auto.
  - intro. destruct H1. rewrite H1 in H0. now apply Not_In_False in H0.
    apply not_in_cons in H0. destruct H0. firstorder.
  - intro. apply not_in_cons in H0. destruct H0. apply not_in_cons in H1. destruct H1.
    destruct H. symmetry in H. now apply H1 in H. destruct H. symmetry in H. now apply H0 in H.
    now apply H2 in H.
Qed.


Theorem Permutation_relf {X:Type} : forall l: list X,
  Permutation l l.
Proof.
  intros. induction l. constructor. now repeat constructor. 
Qed.

Fixpoint length_nat{X:Type}(tl:list X):nat:=
  match tl with
  |[] => 0
  |t::tl' => 1 + length_nat tl'
  end.

Lemma Permutation_length{X:Type}: forall (l1 l2:list X),
  Permutation l1 l2 -> length_nat l1 = length_nat l2.
Proof.
  intros. induction H;simpl. easy. now rewrite IHPermutation.
  easy. now rewrite IHPermutation1.
Qed.


Lemma Permutation_nil_r {X:Type}: forall (l: list X),
  Permutation l [] -> l = [].
Proof.
  intros. apply Permutation_length in H. simpl in H.
  induction l. easy. simpl in H. inversion H.
Qed.

Lemma Permutation_nil_l {X:Type} : forall (l: list X),
  Permutation [] l -> l = [].
Proof.
  intros. apply Permutation_sym in H. 
  now apply Permutation_nil_r.
Qed.

