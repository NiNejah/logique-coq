(* Insertion sort development *)
(* Initially by P. Casteran *)

Set Implicit Arguments.
(* Importing Libraries *)

Require Import List String FunInd.
Require Import Sorting.Permutation RelationClasses.

(* List and String notations *)

Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.
Check (fun i:nat => cons  i (cons i nil)).

Check [6;8;7;9].
Check ["Anne"; "Pierre"; "Pascale"; "Pascal"; "42"].

Coercion is_true : bool >-> Sortclass.

Check is_true.

Section Insertion_sort.
  Variable A : Type.
  Variable leb : A -> A -> bool.
  Notation "a <= b" := (leb a b).
  Notation "a < b" := (leb b a = false).
  
  (** ** Insertion sort *)

  Fixpoint insert (a:A) (l: list A) : list A:=
    match l with
        [] => [a]
      | b::l' => if  a <= b then a::l else b::insert a l'
    end.

  Fixpoint sort (l: list A) : list A :=
    match l with
        nil => nil
      | a::l' => insert a (sort l')
    end.

  (** ** Formal specification *)
  
  Inductive Sorted : list A -> Prop :=
    Sorted_0 : Sorted nil
  | Sorted_1 : forall a, Sorted [a]
  | Sorted_2 : forall a b l, a <= b  ->
                        Sorted (b::l) ->
                        Sorted (a::b::l).
  
  Hint Constructors Sorted: sorted.
  Check Sorted_ind.

  Definition Total (comp : A -> A -> bool) :=
    forall a b, comp a b = false -> comp b a = true.

  Hypothesis leb_total : Total leb. 
  

  
  Definition Sort_spec (f : list A -> list A) :=
    forall l, let l' := f l in
         Permutation l' l /\ Sorted l'.

  Lemma insert_perm : forall x l, Permutation (x :: l) (insert x l).
  Proof.
    induction l.
    - trivial.
    - simpl. 
      case (leb x a); trivial.
      + transitivity (a:: x :: l).
        *  Search (Permutation (?x :: ?y ::?l) (?y :: ?x :: ?l)).
           apply perm_swap.
        * auto.   
  Qed.

  Lemma insert_sorted : forall  x l , Sorted l -> Sorted (insert x l).
  Proof.
    induction 1;cbn; auto with *.
    case_eq (leb x a);  auto with *.
    cbn in *; case_eq (leb x a) ; case_eq (leb x b);  auto with *.
    intros H1 ; rewrite H1 in IHSorted; auto with *.
  Qed.

  Hint Resolve insert_sorted insert_perm: sort.
  Hint Constructors Permutation: perm.

  Lemma sort_perm : forall l, Permutation (sort l) l.
  Proof.
    induction l.
    - reflexivity.
    - transitivity (a:: sort l); auto; 
      symmetry; apply insert_perm.
  Qed.

  Lemma sort_sorted : forall l, Sorted (sort l).
  Proof.
    induction l;auto with *.
    now apply insert_sorted.
  Qed.

  Theorem sort_correct : Sort_spec sort.
  Proof.
    split.
    - apply sort_perm.
    - apply sort_sorted.
  Qed.

End Insertion_sort.

Check sort.
Check sort_correct. 

Search (nat->nat->bool).

Compute sort Nat.leb [8;6;9;3;7;8].
Compute sort (fun n p => Nat.leb p n) [8;6;9;3;7;8].

Require Import String.

Search (string->nat).
Open Scope string_scope.

Compute let string_leb s s' :=  Nat.leb (length s) (length s')
in
        sort string_leb
             ["cb"; "ab"; "cd"; "abcd"].

Definition string_leb s s' :=  Nat.leb (length s) (length s').

Compute sort string_leb
        ["cb"; "ab"; "cd"; "abcd"].

Lemma  nat_leb_total :  Total Nat.leb.
Proof.
  red; induction a; destruct b; simpl; try discriminate; auto.
Qed.

Lemma string_leb_total : Total string_leb.
Proof.  
 intros s s';apply nat_leb_total.
Qed. 

Definition sort_correct_string :=
  sort_correct string_leb_total.

Check sort_correct_string.

Extraction Language OCaml.

Recursive Extraction sort.



