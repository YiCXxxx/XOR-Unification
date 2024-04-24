From XORUnif Require Export ListTermRepresentation.

From CoLoR Require Import
  LogicUtil BoolUtil ListUtil EqUtil ListDec NatUtil ListMax.



(* 
  return the list of variables in the term
*)

Fixpoint vars_term (t: term) : list var :=
  match t with
  | C _ => []
  | V x => [x]
  | Oplus t1 t2 => ((vars_term t1) ++ ( vars_term t2))
  end.





(*Term Beq*)
Local Open Scope lazy_bool_scope.

Scheme Equality for string.
Scheme Equality for list.

Lemma string_beq_ok (s1 s2: string):
 string_beq s1 s2 = true <-> s1 = s2.
Proof.  
 split.
 - intros. now apply (internal_string_dec_bl).
 - intros; subst. now apply internal_string_dec_lb.
Qed.

Definition beq_var := string_beq.
Definition eq_dec_var := string_eq_dec.

Lemma beq_var_ok (s1 s2: var):
  beq_var s1 s2 = true <-> s1 = s2.
Proof. 
  exact (string_beq_ok s1 s2).
Qed.

Fixpoint term_beq (t1 t2:term):bool:=
  match t1, t2 with
  |C n, C m => beq_nat n m
  |V v, V w => beq_var v w
  |Oplus t11 t12, Oplus t21 t22 =>
                orb 
                  (andb (term_beq t11 t21) (term_beq t12 t22)) 
                  (andb (term_beq t12 t21) (term_beq t11 t22))
  |_, _ => false
  end.  




(* Reducing *)

Inductive beq_termlist: list term -> list term -> Prop :=
| beq_nil: beq_termlist [] []
| beq_cons x y l l' :  beq_termlist l l' -> beq_termlist (x::l) (y::l')
| beq_swap x y l : beq_termlist (y::x::l) (x::y::l)
| beq_trans l l' l'' : beq_termlist l l' 
                    -> beq_termlist l' l'' -> beq_termlist l l''
| beq_sym l l': beq_termlist l l' -> beq_termlist l' l
| beq_relf l: beq_termlist l l.

Notation "x =+= y" := (beq_termlist x y) (at level 50, left associativity).

Add Parametric Relation : (list term) beq_termlist
    reflexivity proved by @beq_relf
    symmetry proved by @beq_sym
    transitivity proved by @beq_trans
      as eq_rermlist.


Fixpoint OplusTolist (t:term) : list term:=
  match t with
  | Oplus t1 t2 => (OplusTolist t1) ++ (OplusTolist t2)
  | _ => [t]
  end.

Fixpoint NAdd (t:term) (tl:list term) : list term:=
  match tl with
  | nil => [t]
  | t' :: tl' =>
      match term_beq t t' with
      | true => NAdd T0 tl'
      | false => t' :: NAdd t tl'
      end
  end.

Fixpoint NReducing (tl:list term) : list term:=
  match tl with
  |[] => []
  |t::tl' => NAdd t (NReducing tl')
  end.

Lemma NReducingIdpt(lt:list term):
  (NReducing lt) =+= (NReducing (NReducing lt)).
Proof.
  induction lt. 
  -simpl. constructor.
  -simpl.
Admitted.


(*
Delete 1 T0 from the list
Because this will only apply when the list pass throuh NReducing
*)
Fixpoint T0elim(tl:list term) :list term:=
  match tl with
  |[] => []
  |t::tl'=> if term_beq t T0
              then T0elim tl'
              else t::T0elim tl'
  end.


Definition UReducing (tl:list term):list term:=
  match length tl with
  |0 => []
  |1 => tl
  |S _ => match T0elim tl with
          |[] => [T0]
          |_ => T0elim tl
          end
  end.
  

Definition termReducinglist(t:term):list term:=
  UReducing(NReducing(OplusTolist t)).


Fixpoint listbreakOplus'(tl:list term):list term:=
  match tl with
  |[]=>[]
  |t::tl'=>match t with
          |Oplus t1 t2 => t1::t2::(listbreakOplus' tl')
          |_ => t::(listbreakOplus' tl')
  end end.
  
Fixpoint term_Oplus_layers (t:term) : nat :=
  match t with
  |Oplus t1 t2 => 1 + (max (term_Oplus_layers t1) (term_Oplus_layers t2))
  |_ => 0
  end.

Fixpoint term_list_Oplus_layers (tl:list term): nat :=
  match tl with
  |[] => 0
  |t::tl' => max (term_Oplus_layers t) (term_list_Oplus_layers tl')
  end.


Equations listbreakOplus (fuel:nat) (tl:list term): 
list term:=
  listbreakOplus 0 tl => tl;
  listbreakOplus (S n) tl=> 
    listbreakOplus n (listbreakOplus' tl).

Definition purelist(tl:list term): list term:=
  listbreakOplus (term_list_Oplus_layers tl) (tl).

Definition listReducinglist(tl:list term):list term:=
  UReducing(NReducing (purelist tl)).

(*
Inductive NoDup (A : Type) : list A -> Prop :=
	NoDup_nil : NoDup []
  | NoDup_cons : forall (x : A) (l : list A),
                 ~ In x l -> NoDup l -> NoDup (x :: l).
*)

(*
Assumption listReducinglist return reduced termlist
*)

Definition Reduced_TermList(lt:list term):Prop:=
  lt =+= (listReducinglist lt).


Lemma Reduced_Termlist_beq: forall (lt: list term),
  lt =+= (listReducinglist lt).
Proof.
Admitted.

Lemma Reduced_T0: forall (lt:list term),
listReducinglist (T0 :: lt) =+= lt.
Proof.
Admitted.
