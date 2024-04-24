(* 

This file Defines the fourth rewriting rules, sort_term, 
i.e. sort everyterm in certain order in a lTerm.
if a lTerm is sorted, then every term in the lTerm has is in the specfic order we defines.


Then defines the:
- Prop for ltSorted
- function for sort_term

And proves the important theorem:

Theorem sort_ltSorted: forall (l:list term),
   ltSorted(sort_term l).
  - This Theorem says that after sort_term, every term is lt_Sorted

Lemma sort_ltSorted_Permutation: forall(l:list term),
  AReduced l -> Permutation l (sort_term l).

Theorem ltSorted_sort_term: forall (l:list term),
  AReduced l -> ltSorted l -> sort_term l = l.
  - This one is not so important at this moment, but it is very crucial for later proof.

Note:
  * Some Theorem takes in an extra assumptions that the lTerm has to be AReduced first.
    This will not affect the rewrite system because in the whole rewrite system we will just do AReducing first.

  * In our definition for two lTerm to be equivalence, if two lTerms are Permutation of each other then they equivalence
    Lemma listed above stated this.
*)



From XORUnif Require Export UReduced.

(*
This functions serves as the unit compairson between string
*)
Definition Ascii_compare(a b:Ascii.ascii):comparison:=
  BinNat.N.compare (Ascii.N_of_ascii a) (Ascii.N_of_ascii b).

(*
This functions returns a bool if two strings are equal and false otherwise
*)
Fixpoint compare (s1 s2 : string) : comparison :=
  match s1, s2 with
  | EmptyString, EmptyString => Eq
  | EmptyString, String _ _ => Lt
  | String _ _ , EmptyString => Gt
  | String c1 s1', String c2 s2' =>
    match Ascii_compare c1 c2 with
    | Eq => compare s1' s2'
    | ne => ne
    end
  end.


(*
These are simple utilities about compare two string
*)
Definition order_string(s1 s2:string):Prop:=
    match compare s1 s2 with
    | Gt => False
    | _ => True
    end.

Definition order_string_bool(s1 s2:string):bool:=
    match compare s1 s2 with
    | Gt => false
    | _ => true
    end.

Lemma order_string_bool_Prop:forall (s1 s2:string),
  order_string_bool s1 s2 = true <-> order_string s1 s2.
Proof.
  split.
  - intros. unfold order_string_bool in H. unfold order_string.
    destruct(compare s1 s2);auto. inversion H.
  - intros. unfold order_string_bool. unfold order_string in H.
    destruct(compare s1 s2);auto. 
Qed.

Lemma ascii_compare_relf : forall (a: Ascii.ascii),
  Ascii_compare a a = Eq.
Proof.
  intros. unfold Ascii_compare. apply BinNat.N.compare_refl.
Qed.

Lemma Ascii_compare_eq_iff: forall (a b:Ascii.ascii),
  Ascii_compare a b = Eq -> a = b.
Proof.
  intros. unfold Ascii_compare in H. apply BinNat.N.compare_eq_iff in H.
  assert(J:=Ascii.ascii_N_embedding a).
  assert(J1:=Ascii.ascii_N_embedding b).
  rewrite <- J. rewrite <- J1. rewrite H. auto.
Qed.

Lemma Ascii_compare_antisym:forall (a b:Ascii.ascii),
  Ascii_compare a b = CompOpp (Ascii_compare b a).
Proof.
  intros. unfold Ascii_compare. now rewrite BinNat.N.compare_antisym.
Qed.
  
    
Lemma compare_antisym : forall s1 s2 : string,
    compare s1 s2 = CompOpp (compare s2 s1).
Proof.
  intros s1. pattern s1. induction s1;intros.
  - simpl. destruct s2;auto.
  - simpl. destruct s2;auto. simpl. 
    destruct (Ascii_compare a a0) eqn:H;simpl;auto.
    + apply Ascii_compare_eq_iff in H. rewrite H. assert(Ascii_compare a0 a0 = Eq).
      -- unfold Ascii_compare. apply BinNat.N.compare_refl.
      -- rewrite H0. apply IHs1.
    + rewrite Ascii_compare_antisym in H. unfold CompOpp in H. simpl in H. 
      destruct(Ascii_compare a0 a). inversion H. inversion H. now simpl.
    + rewrite Ascii_compare_antisym in H. unfold CompOpp in H. simpl in H.
      destruct(Ascii_compare a0 a). inversion H. now simpl. inversion H.
Qed.
    
Lemma compare_eq_iff : forall s1 s2 : string,
    compare s1 s2 = Eq <-> s1 = s2.
Proof.
  split.
  - generalize dependent s2. generalize dependent s1.
    intros s1. pattern s1. induction s1.
    + destruct s2. auto. intros. inversion H.
    + intros. destruct s2. inversion H. simpl in H. 
      destruct (Ascii_compare a a0) eqn: H2;inversion H.
      f_equal. now apply Ascii_compare_eq_iff in H2.
      now apply IHs1.
  - generalize dependent s2. generalize dependent s1.
    intros s1. pattern s1. induction s1.
    + destruct s2;simpl. auto. intros. inversion H.
    + intros. destruct s2. inversion H. injection H;intros.
      simpl. rewrite H1. rewrite ascii_compare_relf. now apply IHs1.
Qed.


Lemma CompOpp_simpl_gt:forall(x:comparison),
  x = Gt <-> CompOpp x= Lt.
Proof.
  intros. split;intros.
  - destruct x; inversion H. now unfold CompOpp.
  - destruct x; inversion H. auto.
Qed.

Lemma CompOpp_simpl_lt:forall(x:comparison),
  x = Lt <-> CompOpp x= Gt.
Proof.
  intros. split;intros.
  - destruct x; inversion H. now unfold CompOpp.
  - destruct x; inversion H. auto.
Qed.

Lemma Ascii_compare_tran_Gt: forall(s1 s2 s3: Ascii.ascii),
  Ascii_compare s1 s2 = Gt -> Ascii_compare s2 s3 = Gt -> Ascii_compare s1 s3 = Gt.
Proof.
  intros. unfold Ascii_compare in *.
  remember (Ascii.N_of_ascii s1) as b1.
  remember (Ascii.N_of_ascii s2) as b2.
  remember (Ascii.N_of_ascii s3) as b3.
  clear Heqb1 Heqb2 Heqb3.
  apply BinNat.N.compare_gt_iff in H. 
  apply BinNat.N.compare_gt_iff in H0.
  apply BinNat.N.compare_gt_iff. 
  apply BinNat.N.lt_trans with b2;auto.
Qed.



Lemma compare_trans_Gt: forall (s1 s2 s3: string),
  compare s1 s2 = Gt -> compare s2 s3 = Gt -> compare s1 s3 = Gt.
Proof.
  intros s1. pattern s1. induction s1;intros.
  - destruct s2. auto. destruct s3. inversion H. auto.
  - destruct s2. inversion H0. destruct s3; inversion H2. assert(J:=H).
    simpl in H. destruct (Ascii_compare a a0) eqn:H2; try inversion H.
    + destruct s3. auto. simpl in H0. destruct (Ascii_compare a0 a1) eqn:H4; try inversion H0;simpl.
      apply Ascii_compare_eq_iff in H2. rewrite H2. rewrite H4. rewrite H3.
      apply (IHs1 s2); auto. 
      apply Ascii_compare_eq_iff in H2. rewrite H2. rewrite H4. auto.
    + destruct s3; simpl. auto. assert(J2:= H0). simpl in H0. destruct (Ascii_compare a0 a1) eqn:H5.
      -- apply Ascii_compare_eq_iff in H5. rewrite H5 in *. now rewrite H2.
      -- inversion H0.
      -- destruct (Ascii_compare a a1) eqn:H6;auto.
         ++ apply Ascii_compare_eq_iff in H6. rewrite H6 in *.
            rewrite Ascii_compare_antisym in H2. rewrite H5 in H2.
            simpl in H2. inversion H2.
         ++ clear H H0 J J2. assert(J:=Ascii_compare_tran_Gt _ _ _ H2 H5).
            congruence.
Qed.

Lemma compare_refl:forall(v:var),
  compare v v = Eq.
Proof.
  intros. induction v. auto. simpl. rewrite ascii_compare_relf. auto.
Qed.

Lemma order_string_tran:forall(v1 v2 v3:var),
  order_string v1 v2 -> order_string v2 v3 -> order_string v1 v3.
Proof.
  intros. unfold order_string in *. 
  destruct (compare v1 v2)eqn:H12;
  destruct (compare v2 v3)eqn:H23;
  destruct (compare v1 v3)eqn:H13;auto.
  - apply compare_eq_iff in H12. apply compare_eq_iff in H23. 
    rewrite H12 in H13. rewrite H23 in H13. rewrite compare_refl in H13.
    inversion H13.
  - apply compare_eq_iff in H12. rewrite H12 in *. now rewrite H23 in H13.
  - apply compare_eq_iff in H23. rewrite H23 in *. now rewrite H12 in H13.
  - rewrite compare_antisym in H23. destruct (compare v3 v2) eqn:H1; try inversion H23.
    rewrite compare_antisym in H12. destruct (compare v2 v1) eqn:H2; try inversion H12.
    assert(J:= compare_trans_Gt _ _ _ H1 H2). rewrite compare_antisym in J.
    rewrite H13 in J. inversion J.
Qed.




(* =========================================================================== *)

(*
Now we formaly defines the prop for a lTerm to be sorted,
every constant is less than every string
within constant, we use leq to compare
within string, we use compare to compare
*)
Inductive Rvc: term -> term -> Prop:=
|rvv: forall (v1 v2:var), order_string v1 v2 -> Rvc (V v1) (V v2)
|rvc: forall (v:var) (n:nat), Rvc (C n) (V v)
|rcc: forall (n1 n2:nat), n1 <= n2 -> Rvc (C n1) (C n2).

Inductive ltSorted : list term -> Prop :=
| ltSorted_nil : ltSorted []
| ltSorted_cons1 a : ltSorted [a]
| ltSorted_consn a b l :
    ltSorted (b :: l) -> Rvc a b -> ltSorted (a :: b :: l).

Inductive natSorted : list nat -> Prop :=
| sorted_nat_nil :
    natSorted []
| sorted_nat_1 : forall x,
    natSorted [x]
| sorted_nat_cons : forall x y l,
    x <= y -> natSorted (y :: l) -> natSorted (x :: y :: l).

Inductive varSorted : list var -> Prop :=
| sorted_var_nil :
    varSorted []
| sorted_var_1 : forall x,
    varSorted [x]
| sorted_var_cons : forall x y l,
    order_string x y -> varSorted (y :: l) -> varSorted (x :: y :: l).

(*
This function returns true if the term is a constant term
*)
Definition const_term (t:term): bool :=
    match t with
    |C _ => true
    |_ => false
    end.

(*
This function change nat into its corresponding constant term
*)
Definition nat_to_const(n:nat):term:=
  C n.

(*
This function change a list of nat into their corresponding list of constant term
*)
Definition list_nat_to_list_const(ln:list nat):list term:=
  map nat_to_const ln.


Inductive list_of_const:list term -> Prop:=
  |lconst_nil: list_of_const []
  |lconst_cons t l: const_term t = true -> list_of_const l -> list_of_const (t::l).

Lemma list_of_const_from_nat:forall(l:list nat),
  list_of_const (list_nat_to_list_const l).
Proof.
  intros. induction l; simpl. constructor.
  constructor;auto.
Qed.

Fixpoint list_const_to_list_nat (tl:list term):list nat:=
    match tl with
    |[] => []
    | t::tl' => match t with
                |C n => n::(list_const_to_list_nat tl')
                |_ => list_const_to_list_nat tl'
    end end.


Lemma list_of_const_from_term:forall(l:list term),
  list_of_const (list_nat_to_list_const (list_const_to_list_nat l)).
Proof.
  intros. induction l;simpl. constructor.
  destruct a;auto. simpl. constructor;auto.
Qed.

Lemma list_of_const_length_eq:forall(l:list term),
  list_of_const l -> 
    length_nat (list_const_to_list_nat l) = length_nat l.
Proof.
  intros. induction l; simpl. auto. destruct a; try inversion H;subst.
  - simpl. f_equal. now apply IHl.
  - inversion H2.
  - inversion H2.
Qed.

(*
This function insert a nat into the list
*)
Fixpoint insert_nat (i : nat) (l : list nat) :=
  match l with
  | [] => [i]
  | h :: t => if i <=? h then i :: h :: t else h :: insert_nat i t
  end.

Lemma insert_nat_exists: forall (n :nat)(l:list nat),
  exists l1 l2, insert_nat n l = (l1 ++ n :: l2) /\ l1 ++ l2 = l.
Proof.
  intros. induction l.
  - exists nil. exists nil. now simpl.
  - simpl. destruct(n <=? a) eqn:H.
    + apply Nat.leb_le in H. exists nil; exists (a::l). now simpl.
    + destruct IHl. destruct H0. destruct H0.
      rewrite H0. exists(a::x). exists x0. split.
      -- now simpl.
      -- simpl. f_equal. auto.
Qed.

(*
sorting a list of nat
*)
Fixpoint sort_nat (l:list nat):=
  match l with 
  |[] => []
  |n::l' => insert_nat n (sort_nat l')
  end.

(*
simple utilities reflects prop and bool
*)
Lemma leb_false: forall(n x:nat),
(n <=? x) = false -> x <= n.
Proof.
  intros. destruct (n <=? x)eqn:H1. inversion H. 
  apply Nat.leb_gt in H1. lia.
Qed.


(*
helper lemma
*)
Lemma insert_help_ge: forall (a y:nat) (l:list nat),
  a > y -> insert_nat a (y::l) = y :: insert_nat a l.
Proof.
  intros. simpl. destruct (a <=? y)eqn:H1.
  - apply Nat.leb_le in H1. lia.
  - auto.
Qed.

(*
helper lemma
*)
Lemma insert_help_le: forall (a y:nat) (l:list nat),
  a <= y -> insert_nat a (y::l) = a::y::l.
Proof.
  intros. simpl. destruct (a <=? y)eqn:H1.
  - auto.
  - apply Compare_dec.leb_complete_conv in H1. lia.
Qed.

(*
helper lemma
*)
Lemma insert_sorted_nat: forall (n:nat)(l:list nat),
  natSorted l -> natSorted(insert_nat n l).
Proof.
  intros. induction H.
  - simpl. constructor.
  - unfold insert_nat. destruct(n <=? x) eqn:H.
    + constructor. now apply Nat.leb_le. constructor.
    + constructor. now apply leb_false. constructor.
  - simpl. destruct(n <=? x) eqn:H1.
    + constructor. now apply Nat.leb_le. constructor;auto.
    + destruct(n <=? y)eqn:H2. 
      -- constructor. now apply leb_false in H1. 
      constructor. now apply Nat.leb_le. auto. 
      -- constructor;auto. apply Nat.leb_gt in H2. 
         apply (insert_help_ge _ _ l) in H2. rewrite <- H2. auto. 
Qed.


(*
Important theorem about list after sort_nat is indeed sorted
*)
Lemma sort_sorted_nat: forall (l:list nat),
  natSorted (sort_nat l).
Proof.
  intros. induction l.
  - simpl. constructor.
  - simpl. now apply insert_sorted_nat.
Qed.


(*
helper lemma
*)
Lemma insert_nat_Permutation: forall (l:list nat)(n:nat),
  Permutation (n::l) (insert_nat n l).
Proof.
  intros. induction l;simpl.
  - constructor. constructor.
  - destruct (n <=? a). apply Permutation_relf.   
    assert(Permutation (n :: a :: l) (a :: n :: l)). apply perm_swap.
    apply perm_trans with (a::n::l);auto. 
Qed.

(*
Important Theorem about sort_nat does not lose any numbers
*)
Lemma sort_nat_Permutation: forall (l:list nat),
  Permutation l (sort_nat l).
Proof.
  intros. induction l.
  - simpl. constructor.
  - simpl. assert(Permutation (a::l) (a::(sort_nat l))).
    now constructor. apply perm_trans with (a::sort_nat l).
    auto. apply insert_nat_Permutation.
Qed.


Lemma insert_Cterm_ltSorted: forall (l:list nat),
  natSorted l -> ltSorted(list_nat_to_list_const l).
Proof.
  intros. induction H.
  - simpl. constructor.
  - simpl. constructor.
  - simpl in *. constructor. auto. now apply rcc.
Qed.

(*
Exactly same process as sort_nat except now the compare becomes the string version of compare
detailed comment omit
*)
Definition var_term (t:term): bool :=
    match t with
    |V _ => true
    |_ => false
    end.


Definition var_to_Var(v:var):term:=
  V v.

Definition list_var_to_list_Var(lv:list var):list term:=
  map var_to_Var lv.

Inductive list_of_Var:list term -> Prop:=
  |lvar_nil: list_of_Var []
  |lvar_cons t l: var_term t = true -> list_of_Var l -> list_of_Var (t::l).

Lemma list_of_Var_from_var:forall(l:list var),
  list_of_Var (list_var_to_list_Var l).
Proof.
  intros. induction l;simpl. constructor. 
  constructor;auto.
Qed.

Fixpoint list_Var_to_list_var (tl:list term): list var:=
    match tl with
    | [] => []
    | t::tl' => match t with
                |V v => v::list_Var_to_list_var tl' 
                |_ => list_Var_to_list_var tl'
    end end.


Lemma list_of_Var_from_term:forall(l:list term),
  list_of_Var (list_var_to_list_Var (list_Var_to_list_var l)).
Proof.
  intros. induction l;simpl. constructor.
  destruct a;auto. constructor;auto. 
Qed.

Lemma list_of_Var_length_eq:forall(l:list term),
  list_of_Var l -> 
    length_nat (list_Var_to_list_var l) = length_nat l.
Proof.
  intros. induction l; simpl. auto. destruct a; try inversion H;subst.
  - inversion H2.
  - simpl. f_equal. now apply IHl.
  - inversion H2.
Qed.

Fixpoint insert_var (v: var) (l: list var):=
  match l with
  | [] => [v]
  | h :: t => if order_string_bool h v then h :: insert_var v t else v :: h :: t
  end.

Lemma insert_var_exists: forall (v :var)(l:list var),
  exists l1 l2, insert_var v l = (l1 ++ v :: l2)/\ l1 ++ l2 = l.
Proof.
  intros. induction l.
  - exists nil. exists nil. now simpl.
  - simpl. destruct(order_string_bool a v) eqn:H.
    + destruct IHl. destruct H0. destruct H0.
      rewrite H0. exists(a::x). exists x0. split. now simpl. simpl.
      now f_equal.
    + exists nil. exists (a::l). now simpl.
Qed.

Fixpoint sort_var (l:list var):=
  match l with
  |[] => []
  |v::l' => insert_var v (sort_var l')
  end.

Lemma order_string_bool_true:forall (v1 v2: var),
  order_string_bool v1 v2 = true -> varSorted[v1;v2].
Proof.
  intros. constructor. unfold order_string. unfold order_string_bool in H.
  destruct(compare v1 v2)eqn:H1;auto. inversion H. constructor. 
Qed.

Lemma order_string_bool_sym:forall (v1 v2: var),
  order_string_bool v1 v2 = false -> order_string_bool v2 v1 = true.
Proof.
   intros. unfold order_string_bool in *. destruct (compare v1 v2) eqn:H2.
    - inversion H.
    - inversion H.
    - clear H. rewrite compare_antisym. rewrite H2. simpl. auto.
Qed.

Lemma order_string_bool_sym_rev:forall (v1 v2: var),
  order_string_bool v1 v2 = true -> 
    order_string_bool v2 v1 = false \/ v1 = v2.
Proof.
   intros. unfold order_string_bool in *. destruct (compare v1 v2) eqn:H2.
    - apply compare_eq_iff in H2. now right.
    - clear H. rewrite compare_antisym. rewrite H2. simpl. auto.
    - inversion H.
Qed.

Lemma order_string_bool_false:forall (v1 v2: var),
  order_string_bool v1 v2 = false -> varSorted[v2;v1].
Proof.
  intros. constructor. apply order_string_bool_Prop. 
  now apply order_string_bool_sym.
  constructor.
Qed. 

Lemma insert_sorted_var: forall (n:var)(l:list var),
  varSorted l -> varSorted(insert_var n l).
Proof.
  intros. induction H.
  - simpl. constructor.
  - unfold insert_var. destruct(order_string_bool x n) eqn:H.
    + constructor. unfold order_string_bool in H. unfold order_string. 
      destruct (compare x n);auto. inversion H. constructor.
    + now apply order_string_bool_false.
  - simpl. destruct(order_string_bool x n)eqn:H1.
    + destruct(order_string_bool y n)eqn:H2.
      -- constructor. auto. simpl in *. now rewrite H2 in IHvarSorted.
      -- constructor. now apply order_string_bool_Prop. constructor.
         apply order_string_bool_Prop. now apply order_string_bool_sym.
         auto.
    + constructor. apply order_string_bool_Prop. now apply order_string_bool_sym.
      constructor; auto.
Qed.

Lemma sort_sorted_var: forall (l:list var),
  varSorted (sort_var l).
Proof.
  intros. induction l.
  - simpl. constructor.
  - simpl. now apply insert_sorted_var.
Qed.


Lemma insert_var_Permutation: forall (l:list var)(v:var),
  Permutation (v::l) (insert_var v l).
 Proof.
  intros. induction l;simpl.
  - constructor. constructor.
  - destruct (order_string_bool a v) eqn:H.   
    assert(Permutation (v :: a :: l) (a :: v :: l)). apply perm_swap.
    apply perm_trans with (a::v::l);auto. now constructor.
Qed.

Lemma sort_var_Permutation: forall (l:list var),
  Permutation l (sort_var l).
Proof.
  intros. induction l.
  - simpl. constructor.
  - simpl. assert(Permutation (a::l) (a::(sort_var l))).
    now constructor. apply perm_trans with (a::sort_var l).
    auto. apply insert_var_Permutation.
Qed.

Lemma insert_Vterm_ltSorted: forall (l:list var),
  varSorted l -> ltSorted(list_var_to_list_Var l).
Proof.
  intros. induction H.
  - simpl. constructor.
  - simpl. constructor.
  - simpl in *. constructor. auto. now apply rvv.
Qed.





(*
Now important sort_term
The top level ideas are:
filter out constterm, order them
filter out varterm, order them
and append sorted constterm and varterm
*)
Definition sort_constterm(l:list term):list term:=
    list_nat_to_list_const (sort_nat (list_const_to_list_nat l)).

Definition sort_varterm(l:list term):list term:=
    list_var_to_list_Var (sort_var (list_Var_to_list_var l)).

Definition sort_term(l:list term): list term:=
   (sort_constterm l) ++ (sort_varterm l).

(*
Helper Lemma
*)
Theorem sort_const_ltSorted: forall (l:list term),
   ltSorted(sort_constterm l).
Proof.
  intros. induction l; unfold sort_constterm.
  - simpl. constructor.
  - simpl. destruct (const_term a) eqn:H.
    + simpl. destruct a. remember (n :: list_const_to_list_nat l) as l1.
      assert (H2:= sort_sorted_nat l1). now apply insert_Cterm_ltSorted.
      inversion H. inversion H.
    + assert (H2:= sort_sorted_nat (list_const_to_list_nat l)). 
      apply insert_Cterm_ltSorted. destruct a;try inversion H;auto.
Qed.

(*
Helper Lemma
*)
Lemma sort_var_ltSorted: forall (l:list term),
   ltSorted(sort_varterm l).
Proof.
  intros. induction l; unfold sort_varterm.
  - simpl. constructor.
  - simpl. destruct (var_term a) eqn:H.
    + simpl. destruct a. inversion H.
      assert (H2:= sort_sorted_var (v :: list_Var_to_list_var l)). 
      now apply insert_Vterm_ltSorted. 
      assert (H2:= sort_sorted_var (list_Var_to_list_var l)). 
      now apply insert_Vterm_ltSorted. 
    + assert (H2:= sort_sorted_var (list_Var_to_list_var l)).
      apply insert_Vterm_ltSorted. destruct a;try inversion H;auto.
Qed.

(*
Helper Lemma
*)
Lemma sort_CV_cons:forall(n:nat)(lv:list var),
  varSorted lv -> ltSorted((C n)::(list_var_to_list_Var lv)).
Proof.
  intros. induction lv;simpl.
  - constructor.
  - constructor. inversion H; subst.
    + simpl. constructor.
    + simpl in *. constructor. assert(H4:= insert_Vterm_ltSorted (y::l) H3). auto.
      now apply rvv.
    + apply rvc.
Qed.

(*
Helper Lemma
*)
Lemma sort_CV_app:forall (ln:list nat)(lv:list var), 
  natSorted ln -> varSorted lv -> ltSorted ((list_nat_to_list_const ln)++(list_var_to_list_Var lv)).
Proof.
  intros. induction ln.
  - simpl. now apply insert_Vterm_ltSorted.
  - simpl. inversion H;subst. 
    + simpl in *. apply sort_CV_cons. easy.
    + simpl in *. constructor. firstorder. now apply rcc.
Qed. 

(*Important Theorem about sort_term is correctly sorted*)
Theorem sort_ltSorted: forall (l:list term),
   ltSorted(sort_term l).
Proof.
  intros. unfold sort_term. unfold sort_constterm. unfold sort_varterm.
  remember (list_const_to_list_nat l) as ln.
  remember (list_Var_to_list_var l) as lv.
  assert(H:=sort_sorted_nat ln). assert(H1:=sort_sorted_var lv).
  apply sort_CV_app;auto.
Qed.  

(*
simple implication
*)
Lemma list_lenght_correct: forall(l1 l2: list term),
  l1 = l2 -> length_nat l1 = length_nat l2.
Proof.
  intros. rewrite H. auto.
Qed.

(*
simple rewrite rule
*)
Lemma length_nat_app:forall(l1 l2:list term),
  length_nat (l1 ++ l2) = length_nat l1 + length_nat l2.
Proof.
  intros. induction l1;simpl. auto. now f_equal.
Qed. 

(*
simple rewrite rule
*)
Lemma nat_termconst_same_length:forall(l:list nat),
  length_nat l = length_nat (list_nat_to_list_const l).
Proof.
  intros. induction l.
  - simpl. auto.
  - simpl. now rewrite IHl.
Qed.

(*
simple rewrite rule
*)
Lemma nat_insert_increment:forall(n:nat)(l:list nat),
  S(length_nat l) = length_nat (insert_nat n l).
Proof.
  intros. induction l.
  - simpl. auto.
  - simpl. destruct(n <=? a); simpl. auto. now rewrite IHl.
Qed.

(*
simple rewrite rule
*)
Lemma var_termconst_same_length:forall(l:list var),
  length_nat l = length_nat (list_var_to_list_Var l).
Proof.
  intros. induction l.
  - simpl. auto.
  - simpl. now rewrite IHl.
Qed.

(*
simple rewrite rule
*)
Lemma var_insert_increment:forall(n:var)(l:list var),
  S(length_nat l) = length_nat (insert_var n l).
Proof.
  intros. induction l.
  - simpl. auto.
  - simpl. destruct(order_string_bool a n); simpl. auto. now rewrite IHl.
Qed.

(*
simple rewrite rule
*)
Lemma length_nat_0{X:Type}: forall (l:list X),
  length_nat l = 0 <-> l = nil.
Proof.
  split;intros.
  - destruct l. auto. inversion H.
  - now rewrite H.
Qed. 

(*
Lemma about removing the second term the lTerm still remains sorted
*)
Lemma ltSorted_skip:forall(t1 t2:term)(l:list term),
  ltSorted(t1::t2::l)->ltSorted(t1::l).
Proof.
  intros. inversion H;subst. inversion H2;subst. constructor.
  inversion H4;subst; inversion H5; subst.
  - constructor;auto. apply (order_string_tran _ _ v3) in H0. 
    now constructor. auto.
  - constructor;auto. apply rvc.
  - constructor;auto. apply rvc.
  - constructor;auto. apply rcc. lia.
Qed.

(*
if a term is var term and the lTerm is sorted,
then every term after that var term is var term
*)
Lemma ltSorted_v_cons_l_var_list:forall(v:var)(l:list term),
  ltSorted((V v)::l) -> list_of_Var l.
Proof.
  intros. induction l. constructor.
  inversion H;subst. destruct a;try inversion H4;subst. 
  constructor;auto. apply ltSorted_skip in H. auto.
Qed.

(*
Simple implication
*)
Lemma list_of_Var_app:forall(l1 l2:list term),
  list_of_Var (l1 ++ l2 ) <-> list_of_Var l1 /\ list_of_Var l2.
Proof.
  split;intros.
  - split. 
    + induction l1. constructor.
    inversion H;subst. constructor; auto.
    + induction l1. auto. inversion H. auto.
  - destruct H. induction l1. auto. inversion H;subst. constructor;auto.
Qed. 

(*
Simple implication
*)
Lemma sort_varterm_var_list:forall (l:list term),
  list_of_Var (sort_varterm l).
Proof.
  intros. induction l. constructor.
  unfold sort_varterm. destruct a;auto. simpl.
  assert(H:=insert_var_exists v (sort_var (list_Var_to_list_var l))).
  destruct H. destruct H. destruct H. rewrite H. unfold sort_varterm in IHl.
  rewrite <- H0 in IHl. unfold list_var_to_list_Var in *. 
  rewrite map_app in *. apply list_of_Var_app in IHl. destruct IHl.
  apply list_of_Var_app. split. auto. constructor;auto.
Qed.

(*
Simple implication
*)
Lemma list_of_const_app:forall(l1 l2:list term),
  list_of_const (l1 ++ l2 ) <-> list_of_const l1 /\ list_of_const l2.
Proof.
  split;intros.
  - split. 
    + induction l1. constructor.
    inversion H;subst. constructor; auto.
    + induction l1. auto. inversion H. auto.
  - destruct H. induction l1. auto. inversion H;subst. constructor;auto.
Qed. 

(*
filter correctly
*)
Lemma sort_constterm_const_list:forall (l:list term),
  list_of_const (sort_constterm l).
Proof.
  intros. induction l. constructor.
  unfold sort_constterm. destruct a;auto. simpl.
  assert(H:=insert_nat_exists n (sort_nat (list_const_to_list_nat l))).
  destruct H. destruct H. destruct H. rewrite H. unfold sort_constterm in IHl.
  rewrite <- H0 in IHl. unfold list_nat_to_list_const in *. 
  rewrite map_app in *. apply list_of_const_app in IHl. destruct IHl.
  apply list_of_const_app. split. auto. constructor;auto.
Qed.

(*
simple rewrite rule
*)
Lemma list_of_const_lt_var:forall (l:list term),
  list_of_const l -> list_Var_to_list_var l = [].
Proof.
  intros. induction l. auto. simpl.
  inversion H;subst. destruct a;try inversion H2;auto.
Qed.

(*
simple rewrite rule
*)
Lemma list_of_Var_lt_sort:forall (l:list term),
  list_of_Var l -> list_const_to_list_nat l = [].
Proof.
  intros. induction l;simpl;auto. destruct a;try inversion H;subst;simpl;auto.
  inversion H. inversion H4.
Qed.

(*
first element is the smallest
*)
Lemma ltSorted_forall_smallest_nat:forall(n:nat)(l:list term),
  ltSorted(C n::l) -> 
    (forall n0, In n0 (list_const_to_list_nat l) -> n <= n0).
Proof.
  intros. induction l. inversion H0.
  simpl in H0. destruct a.
  - inversion H;subst. inversion H5;subst. inversion H0.
    + rewrite <- H1. auto.
    + apply ltSorted_skip in H. auto.
  - apply ltSorted_skip in H. auto.
  - apply ltSorted_skip in H. auto.
Qed.

(*
if smallest then it will be placed as the first element
*)
Lemma forall_smallest_ltSorted:forall(n:nat)(l:list nat),
  ltSorted(list_nat_to_list_const l)->
  (forall n0, In n0 l -> n <= n0) ->  
    ltSorted(C n::(list_nat_to_list_const l)).
Proof.
  intros. induction l;simpl in *. constructor.
  constructor. auto. apply rcc. assert(H1:=H0 a). auto.
Qed.

(*
if smallest then it will be placed as the first element
*)
Lemma forall_smallest_insert_nat: forall(n:nat)(l:list nat),
(forall n0, In n0 l -> n <= n0 )
-> insert_nat n l = n::l.
Proof.
  intros. induction l. auto.
  assert(In a (a::l)). now left. assert(Ha:=H a H0). simpl.
  assert(H4:=Nat.leb_spec0 n a). inversion H4. auto. lia.
Qed. 

(*
smallest first, sort_nat does not move the position of the smallest
*)
Lemma forall_smallest_sort_cons:forall(n:nat)(l:list nat),
  (forall n0, In n0 l -> n<=n0 )
  -> sort_nat(n::l) = n::(sort_nat l).
Proof.
  intros. induction l. auto. remember (a::l) as al. simpl. 
  assert(J:=forall_smallest_insert_nat n (sort_nat al)). apply J.
  intros. apply H. assert(H2:=sort_nat_Permutation al).
  apply Permutation_sym in H2.
  now assert (L:=Permutation_In _ _ n0 H2 H0). 
Qed.

(*
if lTerm is ltSorted then remove the first element is ltSorted
*)
Lemma ltSorted_remove:forall(t:term)(l:list term),
  ltSorted (t::l) -> ltSorted l.
Proof.
  intros. induction l. constructor.
  inversion H;subst. auto.
Qed.

(*
simple rewrite rule
*)
Lemma lntlc_lctln:forall(l:list nat),
  (list_const_to_list_nat (list_nat_to_list_const l)) = l.
Proof.
  intros. induction l. auto.
  simpl. now f_equal.
Qed.

(*
simple rewrite rule
*)
Lemma lvtlv_lvtlv:forall(l:list var),
  (list_Var_to_list_var (list_var_to_list_Var l)) = l.
Proof.
  intros. induction l. auto. simpl. now f_equal.
Qed.

(*
simple rewrite rule
*)
Lemma lntlc_lctln_filter:forall(l:list term),
  (list_nat_to_list_const(list_const_to_list_nat l))
  = filter (const_term) l.
Proof.
  intros. induction l. auto.
  simpl. destruct a;auto. simpl. now f_equal.
Qed.

(*
simple rewrite rule
*)
Lemma lvtlv_lvtlv_filter:forall(l:list term),
  (list_var_to_list_Var (list_Var_to_list_var l)) 
  = filter (var_term) l.
  Proof.
    intros. induction l. auto.
    simpl. destruct a;auto. simpl. now f_equal.
  Qed.

(*
simple rewrite rule
*)
Lemma ltSorted_cons_sort_nat:forall(n:nat)(l:list term),
  ltSorted(C n::l) -> 
  sort_nat (n::list_const_to_list_nat l) = n :: sort_nat(list_const_to_list_nat l).
Proof.
  intros. assert(J:=ltSorted_forall_smallest_nat n l H).
  simpl.
  assert(J1:=forall_smallest_sort_cons _ _ J). auto.
Qed. 

(*
Similar Lemma as the const version,
detaled comment omit
*)
Lemma varSorted_skip:forall(v1 v2:var)(l:list var),
  varSorted(v1::v2::l) -> varSorted(v1::l).
Proof.
  intros. induction l. constructor.
  inversion H;subst. inversion H4;subst.
  constructor. apply order_string_tran with v2;auto. auto.
Qed.

Lemma varSorted_forall_smallest_var:forall(v:var)(l:list var),
  varSorted(v::l) -> 
    (forall v0, In v0 l -> order_string v v0).
Proof.
  intros. induction l. inversion H0.
  destruct H0.
  - rewrite H0 in *. inversion H;subst. auto.
  - apply IHl;auto. inversion H;subst. now apply varSorted_skip in H.
Qed.

Lemma ltSorted_forall_smallest_var:forall(v:var)(l:list term),
  ltSorted(V v::l) -> 
    (forall v0, In v0 (list_Var_to_list_var l) -> order_string v v0).
Proof.
  intros. induction l. inversion H0.
  simpl in H0. destruct a.
  - inversion H;subst. inversion H5.
  - inversion H;subst. inversion H5;subst. inversion H0.
    + rewrite <- H1. auto.
    + apply ltSorted_skip in H. auto.
  - apply ltSorted_skip in H. auto.
Qed.

Lemma forall_smallest_insert_var: forall(v:var)(l:list var),
(forall v0, In v0 l -> order_string v v0)
-> insert_var v l = v::l.
Proof.
  intros. induction l. auto.
  assert(In a (a::l)). now left. assert(Ha:=H a H0). simpl.
  apply order_string_bool_Prop in Ha.  apply order_string_bool_sym_rev in Ha.
  destruct Ha.
  - rewrite H1. auto.
  - rewrite H1. destruct (order_string_bool a a);auto.
    f_equal. rewrite H1 in IHl. apply IHl. intros. 
    assert(J:=H v0). rewrite <- H1. apply J. now right.
Qed. 

Lemma varSorted_sort_idpt: forall(l:list var),
  varSorted l -> sort_var l = l.
Proof.
  intros. induction H.
  - auto.
  - auto.
  - remember (y::l) as yl. simpl. rewrite IHvarSorted.
    rewrite Heqyl. simpl. 
    apply order_string_bool_Prop in H. 
    apply order_string_bool_sym_rev in H. destruct H.
    + rewrite H. auto.
    + rewrite H. destruct (order_string_bool y y)eqn:H1;auto.
      subst. f_equal. simpl in *. 
      assert(J:=varSorted_forall_smallest_var y l H0).
      apply forall_smallest_insert_var in J. auto.
Qed.

Lemma natSorted_sort_idpt: forall(l:list nat),
  natSorted l -> sort_nat l = l.
Proof.
  intros. induction H.
  - auto.
  - auto.
  - remember (y::l) as yl. simpl. rewrite IHnatSorted.
    rewrite Heqyl. simpl. apply Nat.leb_le in H.
    rewrite H. auto. 
Qed.
      
Lemma forall_smallest_sort_var:forall(v:var)(l:list var),
  (forall v0, In v0 l -> order_string v v0 )
  -> sort_var(v::l) = v::(sort_var l).
Proof.
  intros. induction l. auto. 
  remember (a::l) as al. simpl. 
  assert(J:=forall_smallest_insert_var v (sort_var al)). apply J.
  intros. apply H. assert(H2:=sort_var_Permutation al).
  apply Permutation_sym in H2.
  now assert (L:=Permutation_In _ _ v0 H2 H0). 
Qed.

Lemma ltSorted_cons_sort_var:forall(v:var)(l:list term),
  ltSorted(V v::l) -> 
  sort_var (v::list_Var_to_list_var l) = v :: sort_var(list_Var_to_list_var l).
Proof.
  intros. assert(J:=ltSorted_forall_smallest_var v l H).
  simpl.
  assert(J1:=forall_smallest_sort_var _ _ J). auto.
Qed. 


(*
Important theorem about sort_term being idempotent
*)
Theorem ltSorted_sort_term: forall (l:list term),
  AReduced l -> ltSorted l -> sort_term l = l.
Proof.
  intros. induction H0.
  - auto.
  - unfold sort_term. unfold sort_constterm. unfold sort_varterm. destruct a;simpl;auto.
    inversion H.
  - inversion H;subst. 
    + firstorder. inversion H1;subst.
      -- assert(J:=sort_ltSorted (V v::l)). rewrite H2 in J.
         apply ltSorted_v_cons_l_var_list in J. unfold sort_term.
         unfold sort_constterm. simpl. apply list_of_Var_lt_sort in J.
         rewrite J. simpl. f_equal. unfold sort_term in H2. unfold sort_constterm in H2.
         simpl in H2. rewrite J in H2. simpl in H2. unfold sort_varterm in *. 
         simpl. auto.
      -- assert(ltSorted (C n :: C n2 :: l)). now constructor.
         remember (C n2::l) as nl. unfold sort_term.
         unfold sort_constterm. 
         assert (J:= ltSorted_cons_sort_nat n nl H4). 
         simpl list_const_to_list_nat. rewrite J. simpl. f_equal.
         unfold sort_varterm. simpl. auto.
    + firstorder. destruct b; try inversion H1;subst.
      assert(ltSorted(V v::V v0::l)). now constructor.
      unfold sort_term. assert(K:=ltSorted_v_cons_l_var_list v0 l H0).
      apply list_of_Var_lt_sort in K. unfold sort_constterm. simpl.
      rewrite K. simpl. unfold sort_varterm. unfold sort_term in H2. 
      unfold sort_constterm in H2. simpl in H2. rewrite K in H2. simpl in H2.
      remember (V v0::l) as vl. simpl list_Var_to_list_var.
      assert (J:= ltSorted_cons_sort_var v vl H4). rewrite J. simpl. f_equal.
      auto.
Qed.

(*
simple rewrite rule
*)
Lemma nat_termconst_app: forall(l1 l2:list nat),
  list_nat_to_list_const (l1 ++ l2) = list_nat_to_list_const l1 ++ list_nat_to_list_const l2.
Proof.
  intros. induction l1. now simpl. simpl. now f_equal.
Qed.


(*
Some simple rules about Permutation and count_occ
*)
Lemma Permutation_map{X Y:Type}: forall(l1 l2:list X) (f:X -> Y),
  Permutation l1 l2 -> Permutation (map f l1) (map f l2).
Proof.
  intros.
  induction H;simpl.
    - constructor.
    - constructor;auto. 
    - constructor.
    - apply perm_trans with (map f l');auto. 
Qed.

Lemma count_occ_Permutation {X}: forall
(eq_dec : forall x y : X, {x = y} + {x <> y})
(l1 l2 :list X),
  (forall t: X, count_occ eq_dec l1 t = count_occ eq_dec l2 t) 
  -> Permutation l1 l2.
Proof.
  apply Permutation_count_occ.
Qed.

Lemma count_occ_lt_ln:forall(n:nat)(l:list nat),
  count_occ term_beq_syn_dec (list_nat_to_list_const l) (C n) 
  = count_occ eq_dec l n.
Proof.
  intros. induction l;simpl.
  - auto.
  - destruct (term_beq_syn_dec (nat_to_const a) (C n)).
    + unfold nat_to_const in e. inversion e. destruct(eq_dec n n) eqn:Hn.
      lia. exfalso. now apply n0.
    + unfold nat_to_const in n0. destruct(eq_dec a n). rewrite e in n0.
      exfalso;now apply n0. auto.
Qed.

Lemma Permutation_lntlc:forall (l1 l2 :list nat),
  Permutation (list_nat_to_list_const l1) (list_nat_to_list_const l2)
  -> Permutation l1 l2.
Proof.
  intros. assert(H1:=count_occ_Permutation eq_dec l1 l2). apply H1.
  intros. apply Permutation_count_occ. apply H1; intros.
  repeat rewrite <- count_occ_lt_ln. now apply Permutation_count_occ.
Qed.

Lemma count_occ_lt_lv:forall(v:var)(l:list var),
  count_occ term_beq_syn_dec (list_var_to_list_Var l) (V v) 
  = count_occ eq_dec_var l v.
Proof.
  intros. induction l;simpl.
  - auto.
  - destruct (term_beq_syn_dec (var_to_Var a) (V v)).
    + unfold nat_to_const in e. inversion e. destruct(eq_dec_var v v) eqn:Hn.
      lia. exfalso. now apply n.
    + unfold var_to_Var in n. destruct(eq_dec_var a v). rewrite e in n.
      exfalso;now apply n. auto.
Qed.

Lemma Permutation_lvtlv:forall (l1 l2 :list var),
  Permutation (list_var_to_list_Var l1) (list_var_to_list_Var l2)
  -> Permutation l1 l2.
Proof.
  intros. assert(H1:=count_occ_Permutation eq_dec_var l1 l2). apply H1.
  intros. apply Permutation_count_occ. apply H1; intros.
  repeat rewrite <- count_occ_lt_lv. now apply Permutation_count_occ.
Qed.

Lemma insert_nat_comm:forall (n1 n2:nat)(l:list nat),
  insert_nat n1(insert_nat n2 l) = insert_nat n2(insert_nat n1 l).
Proof.
  intros. induction l.
  - simpl. destruct(n1 <=? n2)eqn:H; destruct (n2<=? n1)eqn:H1;auto.
    + apply Nat.leb_le in H. apply Nat.leb_le in H1. assert(n1 = n2) by lia.
      now rewrite H0.
    + apply Compare_dec.leb_iff_conv in H. apply Compare_dec.leb_iff_conv in H1.
      lia.
  - simpl. destruct(n2<=?a) eqn:H;destruct(n1<=?a)eqn:H1.
    + simpl. destruct (n1 <=? n2)eqn:H2; destruct (n2 <=? n1)eqn:H3;auto.
      -- apply Nat.leb_le in H2. apply Nat.leb_le in H3.
         assert(n1 = n2) by lia. now rewrite H0.
      -- now rewrite H.
      -- now rewrite H1.
      -- apply Compare_dec.leb_iff_conv in H2. 
         apply Compare_dec.leb_iff_conv in H3. lia.  
    + simpl. destruct (n1 <=? n2)eqn:H2; destruct (n2 <=? n1)eqn:H3;auto.
      -- apply Nat.leb_le in H2. apply Nat.leb_le in H3.
         assert(n1 = n2) by lia. rewrite H0 in *. now rewrite H in H1.
      -- apply Nat.leb_le in H2. apply Nat.leb_le in H.
         apply Compare_dec.leb_iff_conv in H1. lia. 
      -- rewrite H1. rewrite H. auto.
      -- apply Compare_dec.leb_iff_conv in H2. 
         apply Compare_dec.leb_iff_conv in H3. lia.
    + simpl. destruct (n1 <=? n2)eqn:H2; destruct (n2 <=? n1)eqn:H3;auto.
      -- apply Nat.leb_le in H2. apply Nat.leb_le in H3.
         assert(n1 = n2) by lia. rewrite H0 in *. now rewrite H in H1.
      -- rewrite H1. rewrite H. auto.
      -- apply Nat.leb_le in H1. apply Nat.leb_le in H3.
         apply Compare_dec.leb_iff_conv in H. lia.
      -- apply Compare_dec.leb_iff_conv in H2. 
         apply Compare_dec.leb_iff_conv in H3. lia.
    + simpl. destruct (n1 <=? n2)eqn:H2; destruct (n2 <=? n1)eqn:H3;auto.
      -- apply Nat.leb_le in H2. apply Nat.leb_le in H3.
         assert(n1 = n2) by lia. rewrite H0 in *. now rewrite H in H1.
      -- rewrite H1. rewrite H. now f_equal.
      -- rewrite H1. rewrite H. now f_equal.
      -- apply Compare_dec.leb_iff_conv in H2. 
         apply Compare_dec.leb_iff_conv in H3. lia.
Qed.

Lemma Permutation_sort_constterm:forall (l1 l2:list term),
  Permutation l1 l2 -> Permutation (sort_constterm l1) (sort_constterm l2).
Proof.
  intros. induction H.
  - unfold sort_constterm. simpl. constructor.
  - unfold sort_constterm. destruct x;simpl; auto. 
    unfold sort_constterm in IHPermutation. 
    apply Permutation_map. 
    assert(J1:=insert_nat_Permutation (sort_nat (list_const_to_list_nat l)) n).
    assert(J2:=insert_nat_Permutation (sort_nat (list_const_to_list_nat l')) n).
    apply Permutation_sym in J1. rewrite J1.
    apply Permutation_sym in J2. rewrite J2. constructor.
    apply Permutation_lntlc. auto.
  - unfold sort_constterm. destruct x; destruct y; simpl;try apply Permutation_relf.
    rewrite insert_nat_comm. apply Permutation_relf.
  - rewrite IHPermutation1. auto.
Qed.


Lemma insert_var_comm:forall (v1 v2:var)(l:list var),
  insert_var v1(insert_var v2 l) = insert_var v2(insert_var v1 l).
Proof.
  intros. induction l.
  - simpl. destruct(order_string_bool v2 v1)eqn:H; 
    destruct(order_string_bool v1 v2)eqn:H1;auto;
    unfold order_string_bool in H; unfold order_string_bool in H1.
    + destruct (compare v2 v1) eqn:H2. apply compare_eq_iff in H2.
      now rewrite H2. rewrite compare_antisym in H2. unfold CompOpp in H2.
      destruct (compare v1 v2);try inversion H2. inversion H1. inversion H.
    + destruct (compare v2 v1) eqn:H2. inversion H. inversion H.
      rewrite compare_antisym in H2. unfold CompOpp in H2.
      destruct (compare v1 v2);try inversion H2. inversion H1. 
  - simpl. destruct (order_string_bool a v2) eqn:H1;
    destruct(order_string_bool a v1)eqn:H2.
    + simpl. rewrite H1. rewrite H2. now rewrite IHl.
    + simpl. rewrite H2. rewrite H1. 
      destruct (order_string_bool v1 v2)eqn:H3.
      -- auto. 
      -- unfold order_string_bool in H1, H2, H3.
      destruct(compare a v2) eqn:H11; destruct(compare a v1)eqn:H12; destruct(compare v1 v2)eqn:H13;
      inversion H1;inversion H2;inversion H3.
        ++ apply compare_eq_iff in H11. rewrite H11 in H12. rewrite compare_antisym in H12.
           apply CompOpp_simpl_gt in H13. rewrite H12 in H13. inversion H13. 
        ++ assert(H4:=compare_trans_Gt a v1 v2). firstorder. rewrite H in H11. inversion H11.
    + simpl. destruct (order_string_bool v2 v1) eqn:H3. destruct (order_string_bool a v1) eqn:H4.
      -- rewrite H1. auto.
      -- inversion H2.
      -- unfold order_string_bool in H1,H2,H3. destruct (compare a v2) eqn:H11;
         destruct (compare a v1) eqn:H12; destruct (compare v2 v1) eqn:H13; inversion H1; inversion H2; inversion H3;simpl in *.
         ++ apply compare_eq_iff in H12. rewrite H12 in H11. rewrite compare_antisym in H11.
            rewrite CompOpp_simpl_gt in H11. rewrite CompOpp_involutive in H11. now rewrite H11 in H13.
         ++ assert(H4:=compare_trans_Gt a v2 v1 H11 H13). now rewrite H12 in H4.
    + simpl. destruct(order_string_bool v2 v1) eqn:H3.
      -- rewrite H2. destruct (order_string_bool v1 v2) eqn:H4. 
         ++ unfold order_string_bool in H3, H4. destruct(compare v2 v1) eqn:H11.
            --- apply compare_eq_iff in H11. rewrite H1. now rewrite H11.
            --- rewrite compare_antisym in H11. rewrite CompOpp_simpl_lt in H11. rewrite CompOpp_involutive in H11.
                now rewrite H11 in H4.
            --- inversion H3.
         ++ auto.
      -- rewrite H1. destruct (order_string_bool v1 v2) eqn:H4.
        ++ auto.
        ++ unfold order_string_bool in H3, H4. destruct(compare v2 v1) eqn:H11.
            --- inversion H3.
            --- inversion H3.
            --- rewrite compare_antisym in H11. rewrite CompOpp_simpl_gt in H11. rewrite CompOpp_involutive in H11.
                now rewrite H11 in H4.
Qed.

Lemma Permutation_sort_varterm:forall (l1 l2:list term),
  Permutation l1 l2 -> Permutation (sort_varterm l1) (sort_varterm l2).
Proof.
  intros. induction H.
  - unfold sort_varterm. simpl. constructor.
  - unfold sort_varterm. destruct x;simpl; auto. 
    unfold sort_varterm in IHPermutation. 
    apply Permutation_map.
    assert(J1:=insert_var_Permutation (sort_var (list_Var_to_list_var l)) v).
    assert(J2:=insert_var_Permutation (sort_var (list_Var_to_list_var l')) v).
    apply Permutation_sym in J1. rewrite J1.
    apply Permutation_sym in J2. rewrite J2. constructor.
    apply Permutation_lvtlv. auto.
  - unfold sort_varterm. destruct x; destruct y; simpl;try apply Permutation_relf.
    rewrite insert_var_comm. apply Permutation_relf.
  - rewrite IHPermutation1. auto.
Qed.

Lemma Permutation_const_var_app:forall(l1 l2:list term),
  Permutation l1 l2 -> 
  Permutation (sort_constterm l1) (sort_constterm l2) /\
  Permutation (sort_varterm l1) (sort_varterm l2).
Proof.
  intros. split.
  - now apply Permutation_sort_constterm.
  - now apply Permutation_sort_varterm.
Qed.  


(*
Simple utilities about lvtlv and lctln
*)
Lemma lVtlv_app:forall(l1 l2:list term),
  list_Var_to_list_var (l1 ++ l2) = list_Var_to_list_var l1 ++ list_Var_to_list_var l2.
Proof.
  intros. induction l1. auto.
  simpl. destruct a;auto. simpl. now f_equal.
Qed.

Lemma lctln_app:forall(l1 l2:list term),
  list_const_to_list_nat (l1 ++ l2) = list_const_to_list_nat l1 ++ list_const_to_list_nat l2.
Proof.
  intros. induction l1. auto.
  simpl. destruct a;auto. simpl. now f_equal.
Qed.

Lemma lVtlv_const:forall(l:list term),
  list_of_const l -> list_Var_to_list_var l = [].
Proof.
  intros. induction l. auto.
  destruct a;try inversion H;subst;try inversion H2.
  simpl. auto.
Qed.

Lemma lctln_var:forall(l:list term),
  list_of_Var l -> list_const_to_list_nat l = [].
Proof.
  intros. induction l. auto.
  destruct a;try inversion H;subst;try inversion H2.
  simpl. auto.
Qed.

Lemma sort_var_idpt:forall(l:list var),
  sort_var l = sort_var(sort_var l).
Proof.
  intros. assert(H:=sort_sorted_var l).
  apply varSorted_sort_idpt in H. auto.
Qed.

(*
Helper lemma, use the fact that sort_term is idempotent
*)
Lemma sort_varterm_term:forall(l:list term),
  sort_varterm l = sort_varterm (sort_term l).
Proof.
  intros. induction l. auto. unfold sort_term. 
  unfold sort_constterm. unfold sort_varterm.
  destruct a;simpl; auto.
  - rewrite lVtlv_app. 
    assert(J:=list_of_const_from_nat (insert_nat n (sort_nat (list_const_to_list_nat l)))).
    apply lVtlv_const in J. rewrite J. simpl. 
    rewrite lvtlv_lvtlv. rewrite <- sort_var_idpt. auto.
  - rewrite lVtlv_app. 
    assert(J:=list_of_const_from_nat (sort_nat (list_const_to_list_nat l))).
    apply lVtlv_const in J. rewrite J. simpl.
    rewrite lvtlv_lvtlv. 
    assert(L:=sort_sorted_var (list_Var_to_list_var l)).
    assert(L1:=insert_sorted_var v _ L).
    apply varSorted_sort_idpt in L1. rewrite L1. auto.
Qed.
   
(*
Helper lemma, use the fact that sort_term is idempotent
*)
Lemma sort_constterm_term:forall(l:list term),
  sort_constterm l = sort_constterm (sort_term l).
Proof.
  intros. induction l.
  - auto.
  - unfold sort_term. unfold sort_varterm. unfold sort_constterm.
    destruct a;simpl;auto.
    + rewrite lctln_app.
      assert(J:=list_of_Var_from_var (sort_var (list_Var_to_list_var l))).
      apply lctln_var in J. rewrite J. rewrite app_nil_r.
      rewrite lntlc_lctln. 
      assert (J1:= sort_sorted_nat (list_const_to_list_nat l)).
      assert (J2:= insert_sorted_nat n _ J1).
      apply natSorted_sort_idpt in J2. rewrite J2. auto.
    + rewrite lctln_app.
      assert(J:=list_of_Var_from_var (insert_var v (sort_var (list_Var_to_list_var l)))).
      apply lctln_var in J. rewrite J. rewrite app_nil_r.
      rewrite lntlc_lctln. assert(J1:=sort_sorted_nat (list_const_to_list_nat l)).
      apply natSorted_sort_idpt in J1. rewrite J1. auto. 
Qed.

(*
Helper lemma, use the fact that sort_term is idempotent
*)
Lemma sort_constterm_idpt:forall(l:list term),
  sort_constterm l = sort_constterm(sort_constterm l).
Proof.
  intros. induction l. auto.
  unfold sort_constterm. destruct a;simpl;auto.
  rewrite lntlc_lctln. 
  assert (J1:= sort_sorted_nat (list_const_to_list_nat l)).
  assert (J2:= insert_sorted_nat n _ J1).
  apply natSorted_sort_idpt in J2. rewrite J2. auto.
Qed.

(*
Helper lemma, use the fact that sort_term is idempotent
*)
Lemma sort_varterm_idpt:forall(l:list term),
  sort_varterm l = sort_varterm(sort_varterm l).
Proof.
  intros. induction l. auto.
  unfold sort_varterm. destruct a;simpl;auto.
  rewrite lvtlv_lvtlv. 
  assert (J1:= sort_sorted_var (list_Var_to_list_var l)).
  assert (J2:= insert_sorted_var v _ J1).
  apply varSorted_sort_idpt in J2. rewrite J2. auto.
Qed.


Lemma sort_term_eq_const_var_eq: forall(l1 l2:list term),
  sort_term l1 = sort_term l2 
    <-> sort_constterm l1 = sort_constterm l2 
      /\ sort_varterm l1 = sort_varterm l2.
Proof.
  split;intros.
  - split.
    + rewrite sort_constterm_term. rewrite H. 
      now rewrite <- sort_constterm_term.
    + rewrite sort_varterm_term. rewrite H. 
      now rewrite <- sort_varterm_term.
  - destruct H. unfold sort_term. congruence.
Qed.

Lemma sort_const_const_var:forall(l:list term),
  sort_constterm (sort_constterm l ++ sort_varterm l) = 
  sort_constterm (sort_constterm l).
Proof.
  intros. assert(H:=sort_constterm_term l). unfold sort_term in H.
  rewrite <- H. rewrite <- sort_constterm_idpt. auto. 
Qed.

(*
Important theorem about sort_term does not lose any term
*)
Theorem sort_ltSorted_Permutation: forall(l:list term),
  AReduced l -> Permutation l (sort_term l).
Proof.
  intros. unfold sort_term. induction l.
  - unfold sort_constterm. unfold sort_varterm. simpl. constructor.
  - destruct a;inversion H;subst.
    + apply IHl in H1. unfold sort_varterm in *. simpl.
      remember (list_var_to_list_Var (sort_var (list_Var_to_list_var l))) as lv.
      unfold sort_constterm. simpl. 
      assert(Permutation (C n::l) (C n::sort_constterm l ++ lv)). constructor. auto.
      rewrite H0. cut (Permutation (C n::sort_constterm l)(list_nat_to_list_const
      (insert_nat n (sort_nat (list_const_to_list_nat l))))). intros.
      assert(J:=Permutation_app_tail lv H2). auto.
      assert(J1:=insert_nat_Permutation (sort_nat (list_const_to_list_nat l)) n).
      unfold sort_constterm. 
      assert(C n :: list_nat_to_list_const (sort_nat (list_const_to_list_nat l))
      = list_nat_to_list_const (n::(sort_nat (list_const_to_list_nat l)))).
      auto. rewrite H2. apply Permutation_map. apply insert_nat_Permutation.
    + apply IHl in H1. unfold sort_constterm in *. simpl.
      remember (list_nat_to_list_const (sort_nat (list_const_to_list_nat l))) as cl.
      unfold sort_varterm. simpl.
      assert(Permutation (V v::l) (cl ++ V v::sort_varterm l)).
      assert(J1:=Permutation_app_comm cl (V v::sort_varterm l)).
      rewrite J1. simpl. constructor.
      assert(J2:=Permutation_app_comm cl (sort_varterm l)). apply Permutation_sym in J2.
      rewrite J2. auto.
      rewrite H0. apply Permutation_app_head.
      assert(J1:=insert_var_Permutation (sort_var (list_Var_to_list_var l)) v).
      unfold sort_varterm. 
      assert(V v :: list_var_to_list_Var (sort_var (list_Var_to_list_var l))
      = list_var_to_list_Var(v::sort_var(list_Var_to_list_var l))). auto.
      rewrite H2. apply Permutation_map. apply insert_var_Permutation.
Qed.      

(*
Some simple rewrite rules
*)
Lemma Permutation_sort_nat:forall(l1 l2:list nat),
  Permutation l1 l2 -> sort_nat l1 = sort_nat l2.
Proof.
  intros. induction H;simpl.
  - auto.
  - now rewrite IHPermutation.
  - now rewrite insert_nat_comm.
  - congruence.
Qed.

Lemma Permutation_sort_var:forall(l1 l2:list var),
  Permutation l1 l2 -> sort_var l1 = sort_var l2.
Proof.
  intros. induction H;simpl.
  - auto.
  - now rewrite IHPermutation.
  - now rewrite insert_var_comm.
  - congruence.
Qed.

Lemma sort_nat_idpt:forall(l:list nat),
  sort_nat l = sort_nat(sort_nat l).
Proof.
  intros. assert(H:=sort_sorted_nat l). 
  apply natSorted_sort_idpt in H. now rewrite H.
Qed.

Lemma Permutation_sort_same: forall(l1 l2:list term),
  Permutation l1 l2 -> sort_term l1 = sort_term l2.
Proof.
  intros. unfold sort_term.
  apply Permutation_const_var_app in H. destruct H.
  assert(sort_constterm l1 = sort_constterm l2).
  {unfold sort_constterm in *. apply Permutation_lntlc in H. f_equal.
   apply Permutation_sort_nat in H. repeat rewrite <- sort_nat_idpt in H. auto.
  }
  assert(sort_varterm l1 = sort_varterm l2).
  {unfold sort_varterm in *. apply Permutation_lvtlv in H0. f_equal.
  apply Permutation_sort_var in H0. repeat rewrite <- sort_var_idpt in H0. auto.
 }
  congruence.
Qed.

Lemma Permutation_rev_l: forall(l:list term),
  Permutation l (rev l).
Proof.
  intros. induction l.
  - simpl. constructor.
  - simpl. assert(H:=Permutation_app_comm [a] (rev l)).
    simpl in H. apply perm_trans with (a :: rev l). now constructor. 
    auto.
Qed.

Lemma sort_constterm_comm:forall(l1 l2:list term),
  sort_constterm(l1++l2)=sort_constterm(l2++l1).
Proof.
  intros. unfold sort_constterm.
  f_equal. apply Permutation_sort_nat. repeat rewrite lctln_app.
  apply Permutation_app_comm.
Qed.

Lemma sort_varterm_comm:forall(l1 l2:list term),
  sort_varterm(l1++l2)=sort_varterm(l2++l1).
Proof.
  intros. unfold sort_varterm.
  f_equal. apply Permutation_sort_var. repeat rewrite lVtlv_app.
  apply Permutation_app_comm.
Qed.

Lemma sort_comm:forall(l1 l2:list term),
  sort_term(l1 ++ l2)=sort_term(l2 ++ l1).
Proof.
  intros. unfold sort_term.
  rewrite sort_varterm_comm. rewrite sort_constterm_comm. auto.
Qed.

Lemma sort_rev: forall(l:list term),
  sort_term(rev l) = sort_term l.
Proof.
  intros. apply Permutation_sort_same. 
  apply Permutation_sym. apply Permutation_rev_l.
Qed.
