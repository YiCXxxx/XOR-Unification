(** Homemade decidability class 

 Time-stamp: <Fri 7/15/22 14:05 Dan Dougherty Decidable.v> 

Largely taken from Gert Smolka's Base library

*)

(* Keep this straight:  

- "decidable" is an attribute of any *Prop*
- "eq_dec" is an attrobute of a *Type*

Note that "P is decidable" can mean any of  THREE different things 

- there is a proof of (P \/ ~P
- there is a function : {P}+{~P}
- there is a function : P -> bool

Helpful:

- Coq.Logic.Decidable is about (P \/ ~P)
https://coq.inria.fr/library/Coq.Logic.Decidable.html

- EquivDec is about sumbool-decidability of setoid equivalences
https://coq.inria.fr/library/Coq.Classes.EquivDec.html

- as is UPenn's CoqEqDec
Https://www.cis.upenn.edu/~plclub/metalib/current/html/CoqEqDec.html

 UPenn's CoqEqDec is about optimizing that when the setoid really is eq


*)

From Coq Require Import List.   Import ListNotations.
From Coq Require Import Bool.

(* Arithmetic comparisions *)
From Coq Require Import Compare_dec.

(** * Decidability *)

(* ----------------------- *)
(** Don't use the names everyone else does, so I can understand when
I'm using mine *)
Class Decbl (P : Prop) := dcd : {P} + {~ P}.
#[export]
Hint Unfold Decbl : core.


Class DecblEq (T : Type) := eq_dec : forall (x y: T),  { x = y } + { x <> y }.
#[export]
Hint Unfold DecblEq : core.

(* Class DecblEq (T : Type) := eqdec : forall (x y:T), Decbl (x=y). *)
(* #[export] *)
(* Hint Unfold DecblEq : core. *)

(* don't fully understand this 

(3)   (decision P D)  is a value    for P:Prop and D: dec P
    specifically, (decision P D) has type (dec P)
    
  indeed, (decision P D) is precisely D.
  but with implit arguments, ie
  Arguments decision P {D}
  the effect is that, eg, 
  (decision (x=y)) has type {x=y}+{~x=y}
  
  explictly would have [for x y : nat, say]
  (@decision (x=y) (nat_eq_dec x y)) : {x=y}+{~ x=y}
  since (x=y): Prop and (nat_eq_dec x y): (eq_dec nat)

  The value that (decision P D) names is either 
  a proof of P or a proof of ~P.

  So in programming we can match on it, ie do things like
     [ if (decision (x=y) then ... else ... ]

*)
(*
Definition decision (P : Prop) (D : Decbl P) : Decbl P := D.
Tactic Notation "decide" constr(p) :=
  destruct (decision p).
Tactic Notation "decide" constr(p) "as" simple_intropattern(i) :=
  destruct (decision p) as i.
*)

(* #[export]
Hint Extern 4  =>
match goal with
  | [  |- dcd ?p ] => exact (decision p)
end : core.
*)

(* @@ Don't really understand these... from stpp *)
Global Hint Mode Decbl ! : typeclass_instances.
Global Arguments dcd _ {_} : simpl never, assert.
(* Arguments dcd _ {_}. *)


(** ====================================== *)
(** General transfer from boolean eq to sumbool decidability *)

(* Given a boolean equality function and suitable proofs that it
yields [=] and [<>], conclude decidability *)
Definition beq_to_eqdec
  {T: Type}
  (beq: T -> T -> bool)
  (beq_ok : forall (x y : T), beq x y = true <-> x=y)
  (x y : T) :  {x=y}+{~x=y} .
    destruct (beq x y) eqn:e.
  - left. now apply (beq_ok x y).
  - right. intros Heq. subst.
    assert (ha: beq y y = true) by now apply (beq_ok).
    congruence.
Defined.


(* *********************************** *)
(** * Connecting sumbool with booleans *)
(* *********************************** *)

Definition sumbool_to_bool :
  forall P Q : Prop, {P} + {Q} -> bool :=
  fun P Q sb => if sb then true else false.

Arguments sumbool_to_bool {P} {Q} _.

Lemma sumbool_to_bool_correct_left 
  (P Q :Prop) (sb :  {P} + {Q}) :
  (@sumbool_to_bool P Q sb) = true -> P.
Proof.  
  intros H.
  unfold sumbool_to_bool in H.
  destruct sb as [y | n]; easy.
Qed.

Lemma sumbool_to_bool_correct_right
  (P Q :Prop) (sb :  {P} + {Q}) :
  (@sumbool_to_bool P Q sb) = false -> Q.
Proof.  
  intros H.
  unfold sumbool_to_bool in H.
  destruct sb as [y | n]; easy.
Qed.

(** NB: don't expect iff in the above. 
Suppose P = Q ! 

But in the case Q is ~P we do get iff:
 *)

Definition dec_to_bool 
  (P : Prop) (sb: {P} + {~ P}) :=
  @sumbool_to_bool P (~P) sb.
Arguments dec_to_bool {P} _.

Lemma dec_to_bool_correct_true P sb :
  (@dec_to_bool P sb) = true <-> P. 
Proof.
  split.
  - unfold dec_to_bool.
    apply sumbool_to_bool_correct_left.
  - intros H.
    unfold dec_to_bool.
    apply not_false_is_true; intros H1.
    assert (H2:= sumbool_to_bool_correct_right P (~P) sb H1 ). 
    easy.
Qed.

Lemma dec_to_bool_correct_false P sb :
  (@dec_to_bool P sb) = false <-> (~ P).
Proof.
  assert (H1:= dec_to_bool_correct_true P sb).
  assert (H2:= not_true_iff_false (dec_to_bool sb)).
  firstorder.
Qed.


(* ----------------------- *)


(** * Library of Examples *)

#[export] 
Instance True_dec :  
  Decbl True :=  left I.

#[export] 
Instance False_dec :  
  Decbl False := right (fun A => A).

#[export] 
Instance impl_dec (P Q : Prop) :  
  Decbl P -> Decbl Q -> Decbl (P -> Q).
Proof.  
  unfold Decbl; tauto. 
Defined.

#[export] 
Instance and_dec (P Q : Prop) :  
  Decbl P -> Decbl Q -> Decbl (P /\ Q).
Proof. 
  unfold Decbl; tauto. 
Defined.

#[export] 
Instance or_dec (P Q : Prop) : 
  Decbl P -> Decbl Q -> Decbl (P \/ Q).
Proof. 
  unfold Decbl; tauto. 
Defined.

#[export]
 Instance not_dec (P : Prop) : 
  Decbl P -> Decbl (~ P).
Proof.
  unfold Decbl; 
  tauto.
Defined.

#[export]
 Instance iff_dec (P Q : Prop) : 
  Decbl P -> Decbl Q -> Decbl (P <-> Q).
Proof. 
  unfold Decbl; tauto.
(* Qed. *)
Defined.

(* Coq standard modules make "not" and "iff" opaque for type class
inference, can be seen with Print HintDb typeclass_instances. *)

Lemma dec_DN' P : 
  Decbl P -> ~~ P -> P.
Proof. 
  unfold Decbl; tauto. 
Qed.

Lemma dec_DN (P: Prop) {H: Decbl P} : 
  ~~ P -> P.
Proof. 
  unfold Decbl in H; tauto. 
Defined.

Lemma dec_DM_and P Q :  
  Decbl P -> Decbl Q -> ~ (P /\ Q) -> ~ P \/ ~ Q.
Proof. 
  unfold Decbl; tauto. 
Qed.

Lemma dec_DM_impl P Q :  
  Decbl P -> Decbl Q -> ~ (P -> Q) -> P /\ ~ Q.
Proof. 
  unfold Decbl; tauto. 
Qed.

Lemma dec_prop_iff (P Q : Prop) : 
  (P <-> Q) -> Decbl P -> Decbl Q.
Proof.
  unfold Decbl; tauto.
Defined.


(** ** Decidable Comparisions (example) *)
#[export]
 Instance nat_le_dec (x y : nat) : Decbl (x <= y) := 
  le_dec x y.


(** ** Decidable equality *)

#[export] 
Instance decbleq_bool :
  DecblEq bool.
Proof.
  intros x y. hnf. decide equality.
Defined.

#[export] 
Instance decbleq_nat :
  DecblEq nat.
Proof.
  intros x y. hnf. decide equality.
Defined.

#[export]
Instance decbleq_prod (A B : Type) :
  (DecblEq A) -> (DecblEq B) -> DecblEq (A * B).
Proof.
  intros HA HB [x1 y1] [x2 y2]. 
  destruct (eq_dec x1 x2);  subst; auto.
  -  destruct (eq_dec y1 y2); subst; auto.
     right. now injection.
  - right; now injection.
Defined.


#[export]
Instance decbleq_option (A: Type) :
  DecblEq A -> DecblEq (option A).
Proof.
  intros HA x y .
    destruct x eqn:ex; destruct y eqn:ey; subst.
    - destruct (eq_dec a a0) ; subst; auto.
      right; now injection.
    - right; easy.    
    - right; easy.
    - auto.
Defined.

(** ** Laws for lists.  Essentially re-packaging standard library facts *)

#[export]
Instance decbleq_list (A: Type) :
  DecblEq A -> DecblEq (list A).
Proof.
  intros HA x y .
  apply List.list_eq_dec.
  apply HA.
Defined.

#[export] 
Instance list_in_dec (X : Type) (x : X) (A : list X) :  
  DecblEq X -> Decbl(In x A).
Proof.
  intros D. now apply List.in_dec. 
Defined.



Lemma list_sigma_forall X ls (p : X -> Prop) (p_dec : forall x, Decbl (p x)) :
  {x | In x ls /\ p x} + {forall x, In x ls -> ~ p x}.
Proof.
  induction ls as [| x ls' IH]; simpl.
  - tauto.
  - destruct IH as [[y [D E]]|D].
    + eauto. 
    + destruct (p_dec x) as [E|E].
      * eauto.
      * right. intros y [[]|F]; auto. 
Defined.

Arguments list_sigma_forall {X} ls p {p_dec}.


#[export]
 Instance list_forall_dec X A (p : X -> Prop) (p_dec : forall x, Decbl (p x)) :
  Decbl (forall x, In x A -> p x).
Proof.
  destruct (list_sigma_forall A (fun x => ~ p x)) as [[x [D E]]|D].
  - right. auto.
  - left. intros x E. apply dec_DN; auto.
Defined.

#[export]
 Instance list_exists_dec X A (p : X -> Prop) (p_dec : forall x, Decbl (p x)) :
  Decbl (exists x, In x A /\ p x).
Proof.
  destruct (list_sigma_forall A p) as [[x [D E]]|D].
  - eauto.
  - right. intros [x [E F]]. exact (D x E F).
Defined.

Lemma list_exists_DM X A  (p : X -> Prop) : 
  (forall x, Decbl (p x)) ->
  ~ (forall x, In x A -> ~ p x) -> exists x, In x A /\ p x.
Proof. 
  intros D E. 
  destruct (list_sigma_forall A p) as [F|F].
  + destruct F as [x F]. eauto.
  + contradiction (E F).
Qed.

Lemma list_cc X (p : X -> Prop) A : 
  (forall x, Decbl (p x)) -> 
  (exists x, In x A /\ p x) -> {x | In x A /\ p x}.
Proof.
  intros D E. 
  destruct (list_sigma_forall A p) as [[x [F G]]|F].
  - eauto.
  - exfalso. destruct E as [x [G H]]. apply (F x); auto.
Defined.


(* @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@ *)

(** ** Working with [dcd] and [eq_dec] *)


Lemma eq_eq_dec (T U: Type) {_: DecblEq T} (x y: T)  (u v: U) :
  x=y ->
  (if eq_dec x y then u else v) = u.
Proof. 
  intros Heq. subst.
  destruct (eq_dec y y); congruence.
Qed.
Arguments eq_eq_dec {T U} _ x y u v.

Lemma neq_eq_dec (T U: Type) {_: DecblEq T} (x y: T)  (u v: U) :
  x<>y ->
  (if eq_dec x y then u else v) = v.
Proof.
  intros Hneq.
  destruct (eq_dec x y); congruence.
Qed.
Arguments neq_eq_dec {T U} _ x y u v.

Lemma y_if_y_dec {U: Type} (P: Prop) {_: Decbl P} (u v: U) :
  P ->
  (if dcd P then u else v) = u.
Proof.
  intros Hneq.
  destruct (dcd P); congruence.
Qed.
Arguments y_if_y_dec {U} P {D} u v.

Lemma n_if_y_dec {U: Type} (P: Prop) {_: Decbl P} (u v: U) :
  ~ P ->
  (if dcd P then u else v) = v.
Proof.
  intros Hneq.
 destruct (dcd P); congruence.
Qed.
Arguments n_if_y_dec {U} P {D} u v.
