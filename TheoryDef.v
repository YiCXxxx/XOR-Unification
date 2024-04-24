(* 

This file defines many of the most basic rules for the development including:

- xor equivalence relations: 
  * Four Axioms for xor: Associativity, Commutativity, Nilepotency and Unity
  * Three Axioms for equivalence relations: Reflexivity, Symmetry, Transitivity
  * One Axioms for Conguruence relation: Compatible

- Some important term utilities functions and Lemmas:
  * term_beq_syn: return true if two terms are syntactically equal
  * term_beq_syn_dec: Decidability term beq
  * const_eqv_to_eq and var_eqv_to_eq stated that if two Var term or two Const term
    are equivalent, then the string or nat they carry are equal.

*)


Require Export Bool.
Require Export Lia.
Require Export List.
Export ListNotations.
Require Export Setoid.           
Require Export Morphisms.
Require Export Relation_Definitions.
Require Export PeanoNat.
Require Export Coq.btauto.Algebra.

From Coq Require Export Strings.String.
From Coq Require Import String.
From Coq Require Export Lists.List.
Require Export Coq.Strings.String.
From Equations Require Export Equations.
From XORUnif Require Export Decidable.

From CoLoR Require Import
  LogicUtil BoolUtil ListUtil EqUtil ListDec NatUtil ListMax.


(* 
In this development, we use string to represent variables.
*)
Definition var := string.

(*
In this development, we consider any Constant(which is a nat), 
any Variable(which is a stirng)
*)

Inductive term: Type :=
| C  :  nat -> term
| V   : var -> term
| Oplus  : term -> term -> term.

Notation "x +' y" := (Oplus x y) (at level 50, left associativity).

(*
The unit is constant 0, i.e.
forall t:term, t +' (C 0) == t
*)
Definition T0:term:= C 0.


(*
Equavalence Relationships Definition: 
*)
Reserved Notation "x == y" (at level 70).

Inductive eqv : term -> term -> Prop :=
| eqvA: forall x y z,    (x +' y) +' z == x +' (y +' z)
| eqvC:   forall x y, x +' y ==  y +' x
| eqvU:    forall x,  T0 +' x  == x
| eqvN:   forall x,  x +' x  == T0

| eqv_ref:   forall x,  x == x  
| eqv_sym:   forall x y,  x == y ->  y == x
| eqv_trans: forall x y z,  x == y ->  y == z ->  x == z
                                                         
| Oplus_compat : forall x x' ,  x == x' -> forall y y' ,
      y == y' -> x +' y ==  x' +' y'
where "x == y" := (eqv x y).

Add Parametric Relation : term eqv
    reflexivity proved by @eqv_ref
    symmetry proved by @eqv_sym
    transitivity proved by @eqv_trans
      as eq_set_rel.

Add Parametric Morphism : Oplus with
      signature eqv ==> eqv ==> eqv as Oplus_mor.
  exact Oplus_compat.
Qed.


(*
Some intuitive lemma checks.
*)

Lemma eqvU' (x: term) :
  x +' T0 ==  x .
Proof. 
  rewrite eqvC. apply eqvU.
Qed.

Lemma cancel_R :
  forall x y z,  x +' z ==  y +' z -> x == y.
Proof.
  intros x y z H.
  cut ((x +' z) +' z ==  (y +' z) +' z).  
  - intros H0. repeat rewrite eqvA in H0.
    repeat rewrite eqvN in H0.
    repeat rewrite eqvU' in H0; easy.
  - rewrite H; easy.
Qed.

Lemma cancel_L :
  forall x y z, z +' x ==  z +' y -> x == y.
Proof.
  intros x y z H.
  rewrite eqvC in H at 1.
  rewrite (eqvC z y) in H.
  apply cancel_R with (z := z); easy.
Qed.

Lemma eqv_eqv0 (s t: term) :
  s == t <-> (s +' t) == T0.
Proof.
  split.
  - intros H.
    rewrite H.  apply eqvN.
  - intros H.
    assert (a : s +' t +' t == T0 +' t).
    + now rewrite H.
    + rewrite eqvA in a.
      rewrite eqvN in a.
      rewrite eqvU in a.
      now rewrite eqvU' in a.
Qed.

(* nat Utilities *)
Definition beq_const := beq_nat.

Lemma beq_nat_same: forall x,
  beq_nat x x = true.
Proof.
  intros. now apply beq_nat_ok.
Qed.

Lemma beq_nat_false: forall x y,
  beq_nat x y = false <-> x <> y.
Proof.
  split;intros.
  - intro. rewrite H0 in H. rewrite beq_nat_same in H. inversion H.
  - intros. assert(a:= bool_dec (beq_nat x y) true). destruct a.
    apply beq_nat_ok in e. now rewrite e in H.
    now apply not_true_is_false in n.
Qed.

(* String Utilities *)
Scheme Equality for string.
Definition beq_string x y:= if string_dec x y then true else false.
Definition beq_var := beq_string.
Definition eq_dec_var := string_eq_dec.

Theorem beq_string_refl : forall (s:string), 
  true = beq_string s s.
Proof. 
  intros s. unfold beq_string. destruct (string_dec s s) as [|Hs].
  - reflexivity.
  - destruct Hs. reflexivity.
Qed.

Theorem beq_var_refl : forall s, 
  beq_var s s = true.
Proof. symmetry. unfold beq_var. apply beq_string_refl. Qed.

Theorem beq_string_true_iff : forall x y : string,
  beq_string x y = true <-> x = y.
Proof.
   intros x y. unfold beq_string.
   destruct (string_dec x y) as [|Hs].
   - subst. split. reflexivity. reflexivity.
   - split.
     + intros contra. inversion contra.
     + intros H. inversion H. subst. destruct Hs. reflexivity.
Qed.

Theorem beq_var_true_iff : forall x y : var,
  beq_var x y = true <-> x = y.
Proof. exact beq_string_true_iff. Qed.

Theorem beq_string_false_iff : forall x y : string,
  beq_string x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- beq_string_true_iff.
  rewrite not_true_iff_false. reflexivity. 
Qed.

Theorem beq_var_false_iff : forall x y : string,
  beq_var x y = false <-> x <> y.
Proof. exact beq_string_false_iff. Qed.



(* 
term utilities 
Note that term_beq_syn here stads for if two terms are equivalence syntactically
*)
Fixpoint term_beq_syn (t1 t2:term):bool:= 
  match t1, t2 with
  |C n1, C n2 => beq_nat n1 n2
  |V v, V w => beq_var v w
  |Oplus t11 t12, Oplus t21 t22 =>
                andb (term_beq_syn t11 t21) (term_beq_syn t12 t22)
  |_, _ => false
  end.  




Lemma term_beq_syn_relf: forall (t : term),
  term_beq_syn t t = true.
Proof.
  intros. induction t.
  - destruct n. now simpl. simpl. apply beq_nat_same.
  - simpl. now apply beq_var_refl.
  - simpl. apply andb_true_intro. now split.
Qed.


Lemma term_syn_true_remove_left: forall (t1 t2 t3:term),
term_beq_syn (t1+'t2) (t1+'t3) = true
  -> term_beq_syn t2 t3 = true.
Proof.
intros. inversion H. 
rewrite term_beq_syn_relf. apply andb_true_l.
Qed.

Lemma term_syn_true_remove_right: forall (t1 t2 t3:term),
term_beq_syn (t2+'t1) (t3+'t1) = true
  -> term_beq_syn t2 t3 = true.
Proof.
intros. inversion H. 
rewrite term_beq_syn_relf. symmetry. apply andb_true_r.
Qed.

Lemma term_syn_true_add_left: forall (t1 t2 t3:term),
term_beq_syn t2 t3 = true ->
  term_beq_syn (t1+'t2) (t1+'t3) = true.
Proof.
intros. simpl. rewrite H. now rewrite term_beq_syn_relf.
Qed.

Lemma term_syn_true_add_right: forall (t1 t2 t3:term),
term_beq_syn t2 t3 = true ->
  term_beq_syn (t2+'t1) (t3+'t1) = true.
Proof.
intros. simpl. rewrite H. now rewrite term_beq_syn_relf.
Qed.

Lemma term_beq_syn_sound: forall (t u: term),
term_beq_syn t u = true -> t = u.
Proof.
intro t. pattern t.
induction t; destruct u; try now simpl.
- assert(a:=eq_dec n n0). destruct a. now rewrite e.
  apply beq_nat_false in n1. simpl. rewrite n1. easy.
- assert(a:=eq_dec_var v v0). destruct a. now rewrite e.
  apply beq_var_false_iff in n. simpl. now rewrite n.
- intros H. simpl term_beq_syn in H. apply andb_prop in H.
  destruct H. apply IHt1 in H. apply IHt2 in H0. now rewrite H, H0.
Qed.

Lemma term_beq_syn_true_iff: forall (t u: term),
term_beq_syn t u = true <-> t = u.
Proof.
split; intros.
now apply term_beq_syn_sound in H.
rewrite H; apply term_beq_syn_relf.
Qed.

Theorem term_beq_syn_false_iff: forall (t u: term),
term_beq_syn t u = false <-> t <> u.
Proof.
split; intros.
- intro. rewrite H0 in H. now rewrite term_beq_syn_relf in H.
- assert (a:= bool_dec (term_beq_syn t u) true). destruct a.
  apply term_beq_syn_true_iff in e. now apply H in e. 
  now apply not_true_is_false in n.
Qed.


Theorem term_beq_syn_eqv: forall (t1 t2 : term),
term_beq_syn t1 t2 = true -> t1 == t2.
Proof. 
intros. apply term_beq_syn_true_iff in H. rewrite H. easy.
Qed.

Lemma term_beq_syn_sym: forall (t1 t2 : term),
term_beq_syn t1 t2 = term_beq_syn t2 t1.
Proof.
intros. destruct t1; destruct t2; try now simpl.
- destruct n; destruct n0;try reflexivity. simpl. 
  assert(a:= eq_dec n n0). destruct a. now rewrite e.
  assert (n0<>n). { unfold not in n1. intro. now apply n1. }
  apply beq_nat_false in n1,H. now rewrite n1, H.
- simpl. assert(a:= bool_dec (beq_var v v0) true).
  destruct a. rewrite e. apply beq_var_true_iff in e. 
  rewrite e. symmetry; apply beq_var_refl.
  apply not_true_is_false in n. apply beq_var_false_iff in n as n1.
  assert (v0<>v). { unfold not in n1. intro. now apply n1. }
  apply beq_var_false_iff in H. now rewrite n,H.
- assert (a:= bool_dec (term_beq_syn (t1_1 +' t1_2) (t2_1 +' t2_2)) true).
  destruct a. rewrite e. apply term_beq_syn_true_iff in e. symmetry in e. 
  apply term_beq_syn_true_iff in e. now rewrite e.
  apply not_true_is_false in n. rewrite n. apply term_beq_syn_false_iff in n.
  assert (t2_1 +' t2_2<>t1_1 +' t1_2 ). 
  { unfold not in n. intro. now apply n. }
  apply term_beq_syn_false_iff in H. now rewrite H.
Qed.

Lemma term_beq_syn_trans: forall (t1 t2 t3: term),
term_beq_syn t1 t2 = true -> term_beq_syn t2 t3 = true
  -> term_beq_syn t1 t3 = true.
Proof.
intros. destruct t1; destruct t2; destruct t3; try inversion H; try inversion H0.
- apply beq_nat_ok in H2, H3. simpl. now rewrite H2, H3.
- apply beq_var_true_iff in H2, H3. simpl. now rewrite H2, H3.
- rewrite H2. apply term_beq_syn_true_iff in H, H0. rewrite H0 in H.
  now apply term_beq_syn_true_iff.
Qed.

Lemma term_neq_const: forall (n m:nat),
n <> m <-> C n <> C m.
Proof.
split.
intros.
- unfold not in *. intro. apply H. now inversion H0.
- intros. unfold not in *. intro.  apply H. now rewrite H0.
Qed.

Lemma term_dec_nat: forall (t:term) (n:nat),
{t = C n}+{t <> C n}.
Proof.
intros. induction t.
- assert (a:=eq_dec n0 n). destruct a.
  rewrite e. now left. right. now apply term_neq_const.
- right. unfold not. intro. inversion H.
- right. unfold not. intro. inversion H.   
Qed.

Lemma term_beq_syn_dec: forall (t1 t2:term),
  {t1 = t2} + {t1 <> t2}.
Proof.
  intros. assert(H:= bool_dec (term_beq_syn t1 t2) true).
  destruct H. apply term_beq_syn_true_iff in e. now left.
  apply not_true_is_false in n. apply term_beq_syn_false_iff in n. now right.
Qed.

Fixpoint const_contains n t :=
  match t with
  | C n' => Nat.eqb n n'
  | V _ => false
  | x +' y => xorb (const_contains n x) (const_contains n y)
  end.

  
Fixpoint var_contains v t :=
  match t with
  | C _ => false
  | V v' => beq_string v v'
  | x +' y => xorb (var_contains v x) (var_contains v y)
  end.

Definition is0 (n:nat):bool:=
  match n with
  |0 => false
  |_ => true
  end.

Fixpoint const_0 t :=
  match t with
  | C n' => is0 n'
  | V _ => false
  | x +' y => (xorb (const_0 x) (const_0 y))
  end.


Lemma const_eqv_contains_0 
      x y : x == y -> const_0 x = const_0 y.
Proof.
  induction 1.
  - simpl. destruct (const_0 x);destruct (const_0 y);destruct (const_0 z);auto.
  - simpl. destruct (const_0 x);destruct (const_0 y);auto.
  - simpl. destruct (const_0 x);auto.
  - simpl. destruct (const_0 x);auto.
  - reflexivity.
  - symmetry;assumption.
  - now rewrite IHeqv1.
  - simpl. congruence.
Qed.

Lemma const_eqv_contains n (Hn:Nat.eqb n 0 = false) 
      x y : x == y -> const_contains n x = const_contains n y.
Proof.
  induction 1;simpl.
  - apply Bool.xorb_assoc_reverse.
  - apply Bool.xorb_comm.
  - simpl. rewrite Hn; apply Bool.xorb_false_l.
  - simpl. rewrite Hn;apply Bool.xorb_nilpotent.
  - reflexivity.
  - symmetry;assumption.
  - transitivity (const_contains n y);assumption.
  - congruence.
Qed.

Lemma var_eqv_contains v
      x y : x == y -> var_contains v x = var_contains v y.
Proof.
  induction 1; simpl.
  - apply Bool.xorb_assoc_reverse.
  - apply Bool.xorb_comm.
  - destruct(var_contains v x);easy.
  - now rewrite xorb_nilpotent.
  - reflexivity.
  - symmetry;assumption.
  - now rewrite IHeqv1.
  - congruence.
Qed.


Arguments Nat.eqb : simpl nomatch.


Lemma const_eqv_to_eq_0: forall n, C n == C 0 -> n = 0.
Proof.
  intros n e.
  assert(H:=const_eqv_contains_0 _ _ e).
  simpl in H. unfold is0 in H. destruct n. easy. inversion H.
Qed.

(*
Here are the Theorems that if two constants are equal then the nat they carry are eq.
*)
Theorem const_eqv_to_eq: forall n m, C n == C m -> n = m.
Proof.
  intros n m e. destruct m.
  - now apply const_eqv_to_eq_0.
  - assert(H:=const_eqv_contains (S m) eq_refl _ _ e).
    simpl in H. rewrite Nat.eqb_refl in H.
    apply PeanoNat.Nat.eqb_eq in H.
    symmetry; exact H.
Qed.

(*
Same thing for variable and string
*)
Theorem var_eqv_to_eq: forall v m, V v == V m -> v = m.
Proof.
  intros v m e. 
  assert(H:=var_eqv_contains v _ _ e).
  simpl in H. rewrite <- beq_string_refl in H.
  symmetry in H. 
  now apply beq_string_true_iff in H.
Qed.

(*
Constant and Variable will never be equal.
*)
Lemma var_neq_const: forall n v, V v == C n -> False.
Proof.
  intros. 
  assert (H1:=var_eqv_contains v (V v) (C n)). apply H1 in H. 
  simpl in H. assert(H2:=beq_string_refl v). now rewrite <- H2 in H.
Qed.
