(* 

This file Defines the first rewriting rules, AReducing, i.e. remove every single oplus in a lTerm,
and we called the reduced form from AReducing - AReduced,
if a lTerm is AReduced, then that lTerm has no +'

Example: 
- [], [V v], [C 1;C 2] is AReduced
- [C1 +' C0], [C 1 ;C 2; C 3 +' C4] is not AReduced

Then defines the:
- Prop for AReduced
- function for AReducing

And proves the important theorem:

Theorem AReducing_lr_Correct_Reduced:forall (tl:lTerm),
  AReduced (AReducing_lr tl).
  - This Theorem says that after AReducing, every term is AReduced

Theorem AReducing_lr_Correct_eqv:forall (tl:lTerm),
  tl =l= (AReducing_lr tl).
  - This Theorem says that after AReducing, it is lTerm_eqv to the original lTerm

Theorem AReduced_AReducing_idpt:forall (tl:lTerm),
  AReduced tl -> AReducing_lr tl = tl.
  - This Theorem says that AReducing is an idempotent function. 
    This one is not so important at this moment, but it is very crucial for later proof.

*)

From XORUnif Require Export ListTermRepresentation.

Inductive AReduced: lTerm->Prop:=
|AReduced_nil: AReduced []
|AReduced_cons_const: forall (tl:list term)(n:nat), 
    AReduced tl -> AReduced ((C n) :: tl)
|AReduced_cons_var: forall (tl:list term)(v:var), 
    AReduced tl -> AReduced ((V v) :: tl).
    
  
(*
If two arbitrary lTerm are AReduced, then the product of appending these two lTerm is also AReduced
*)
Lemma AReduced_app: forall (tl1 tl2:lTerm), 
  AReduced tl1 -> AReduced tl2 -> AReduced (tl1 ++ tl2).
Proof.
  intros. induction tl1.
  - simpl. easy.
  - destruct a; simpl; inversion H;subst; 
    constructor; now apply IHtl1 in H2.
Qed.

(*
If the product of appending two arbitrary lTerm is AReduced, then the left lTerm is AReduced
*)
Lemma AReduced_app_back_left: forall (tl1 tl2:lTerm), 
  AReduced (tl1 ++ tl2) -> AReduced tl1.
Proof.
  intros. induction tl1. constructor.
  inversion H; subst;constructor;firstorder.
Qed.


(*
If the product of appending two arbitrary lTerm is AReduced, then the right lTerm is AReduced
*)
Lemma AReduced_app_back_right: forall (tl1 tl2:lTerm), 
  AReduced (tl1 ++ tl2) -> AReduced tl2.
Proof.
  intro tl2. pattern tl2. induction tl2.
  - intros. now simpl in H.
  - intros. inversion H;subst; apply IHtl2 in H1;auto.
Qed.


(*
If an arbitrary lTerm is AReduced, then remove any term in that lTerm still result in an AReduced lTerm
*)
Lemma AReduced_remove: forall (tl:lTerm)(t:term),
  AReduced (tl) -> AReduced (remove t tl).
Proof.
  intros. induction H. 
  - simpl. constructor.
  - simpl. destruct t. destruct(NatUtil.beq_nat n n0). easy.
    now constructor. now constructor. now constructor.
  - simpl. destruct t. now constructor. destruct(beq_var v v0). easy.
    now constructor. now constructor. 
Qed.

Definition AReducing:= term_to_lTerm.

(*
If an arbitrary lTerm is AReduced, then remove any term in that lTerm still result in an AReduced lTerm
*)
Lemma AReducing_Correct_Reduced: forall (t:term),
  AReduced (AReducing t).
Proof.
  intros. induction t;simpl;try 
  (repeat constructor). now apply AReduced_app.
Qed.
  
(*
lTerm_eqv remains the same after AReducing it
*)
Lemma AReduced_Correct_eqv: forall (t:term),
  t == lTerm_to_term (AReducing t).
Proof.
  apply listTransCorrect_t.
Qed.

(*
function returns truen if the term is in the form of t1 +' t2.
*)
Definition Oplus_term(t:term):bool:=
  match t with 
  |_ +' _ => true
  |_ => false
  end.

(*
Note the differences between AReducing_lr and AReducing
AReducing takes in a term
AReducing_lr takes in a lTerm
*)
Fixpoint AReducing_lr(tl:lTerm):lTerm:=
  match tl with
  |[] => []
  |t::tl' => if (Oplus_term t) 
      then app (term_to_lTerm t) (AReducing_lr tl')
      else t::(AReducing_lr tl')
  end.

(*
These are the important Theorem about a rewrite system
*)
Theorem AReducing_lr_Correct_Reduced:forall (tl:lTerm),
  AReduced (AReducing_lr tl).
Proof.
  intros. induction tl.
  - simpl. constructor.
  - simpl. destruct a; try now constructor.
    simpl. apply AReduced_app.
    + apply AReduced_app;apply AReducing_Correct_Reduced.
    + easy.
Qed.

Theorem AReducing_lr_Correct_eqv:forall (tl:lTerm),
  tl =l= (AReducing_lr tl).
Proof.
  intros. induction tl.
  - simpl. apply lr_relf.
  - destruct a; try now apply lTerm_eqv_cons_compat. simpl.
    assert(a:=lr_compat [a1+'a2] 
    (term_to_lTerm a1 ++ term_to_lTerm a2) tl (AReducing_lr tl)).
    simpl in a. apply a.
    + assert(b:= lr_oplus a1 a2). apply lr_trans with [a1;a2]. easy.
      assert(c:= lr_compat [a1](term_to_lTerm a1)[a2](term_to_lTerm a2)).
      simpl in c. apply c; apply listTransCorrect_lr_term.  
    + easy.
Qed.


Theorem AReduced_AReducing_idpt:forall (tl:lTerm),
  AReduced tl -> AReducing_lr tl = tl.
Proof.
  intros. induction tl.
  - now simpl.
  - inversion H;subst; simpl; f_equal; firstorder.
Qed.


(*
AReducing_lr homomorphism with append
*)
Lemma AReducing_lr_app:forall (l1 l2:lTerm),
  (AReducing_lr l1) ++ (AReducing_lr l2) = AReducing_lr (l1++l2).
Proof.
  intro l1. pattern l1. induction l1.
  - now simpl.
  - intros l3. simpl. destruct (Oplus_term a).
    + rewrite app_assoc_reverse. f_equal;auto.
    + rewrite <- app_comm_cons. f_equal. apply IHl1.
Qed.

(*
a lTerm is AReduced, then the reverse of the lTerm is AReduced
*)
Lemma AReduced_rev:forall (tl:lTerm),
  AReduced tl -> AReduced(rev tl).
Proof.
  intros. induction tl.
  - simpl. constructor.
  - simpl. inversion H;subst. firstorder.
    + apply AReduced_app. easy. constructor. constructor.
    + apply AReduced_app. firstorder. constructor. constructor.
Qed. 

(*
simple rewrite rule for function rev
*)
Lemma rev_simp: forall (t:term)(tl:lTerm),
  rev(tl++[t]) = t ::(rev tl).
Proof.
  intros. induction tl;simpl;auto.
  rewrite IHtl. easy.
Qed. 

(*
simple rewrite rule for function rev
*)
Lemma rev_simp_2: forall (t:term)(tl:lTerm),
  rev(t::tl) = (rev tl)++[t].
Proof.
  intros. induction tl;simpl;auto.
Qed. 

(*
If the rev of a lTerm is AReduced, then the lTerm is AReduced
*)
Lemma rev_AReduced:forall (tl:lTerm),
  AReduced (rev tl) -> AReduced tl.
Proof.
  intros. induction tl.
  - constructor.
  - rewrite rev_simp_2 in H.
    apply AReduced_app_back_left in H as H1. 
    apply AReduced_app_back_right in H.
    firstorder.
    destruct a; try now constructor.
    inversion H.
Qed. 
    