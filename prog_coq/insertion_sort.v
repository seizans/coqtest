(* Definition of insertion_sort and insert *)
Require Import List.
Require Import Arith.

Fixpoint insert (a : nat) (l : list nat) : list nat :=
  match l with
     | nil => a :: nil
     | x :: xs => if leb a x then a :: l else x :: insert a xs
  end.

Fixpoint insertion_sort (l : list nat) : list nat :=
  match l with
    | nil => nil
    | x :: xs => insert x (insertion_sort xs)
  end.

(* example *)
Eval compute in insert 1 nil.
Eval compute in insert 5 (1 :: 4 :: 2 :: 9 :: 3 :: nil).
Eval compute in insertion_sort (2 :: 4 :: 1 :: 5 :: 3 :: nil).


(* Extraction to Haskell *)
Extraction Language Haskell.
(* Extraction configuration,
   but commented out because I failed extracting correct Haskell file. *)
(*
Extract Inductive list => "([])" ["[]" "(:)"].
Extract Inductive bool => "Bool" ["True" "False"].
Extract Inductive nat => Int ["0" "succ"] "(\fO fs n -> if n == 0 then fO () else fS (n-1) )".
*)
Extraction insert.
Extraction insertion_sort.
(* Write Haskell code to file on current directory. Run by coqc. *)
Extraction "insertion_sort.hs" insertion_sort.


(* Proof of property of insertion_sort *)
Require Import Sorting.Permutation.
Require Import Sorting.Sorted.

Lemma insert_perm :
  forall (x : nat) (l : list nat),
  Permutation (x :: l) (insert x l)
.
Proof.
  intro x.
  intro l.
  induction l.
    (* base part *)
    simpl.
    SearchPattern (Permutation ?p ?p).
    apply Permutation_refl.

    (* inductive part *)
    simpl.
    destruct (leb x a).
      (* if leb x a *)
      apply Permutation_refl.

      (* else *)
      Print Permutation.
      rewrite perm_swap.
      apply perm_skip.
      apply IHl.
Qed.

Theorem isort_permutation :
  forall (l : list nat),
  Permutation l (insertion_sort l)
.
Proof.
  induction l.
    simpl.
    apply Permutation_refl.

    simpl.
    Print perm_trans.
    apply perm_trans with (a :: insertion_sort l).
      apply perm_skip.
      apply IHl.

      apply insert_perm.
Qed.


Lemma insert_sorted :
  forall (a : nat) (l : list nat),
  LocallySorted le l -> LocallySorted le (insert a l)
.
Proof.
  intros.
  induction l.
    (* base part *)
    simpl.
    SearchPattern (LocallySorted _ (_ :: nil)).
    apply LSorted_cons1.

    (* inductive part *)
    simpl.
    remember (leb a a0).
    destruct b.
      (* case  a <= a0 *)
      Print LocallySorted.
      apply LSorted_consn.
        apply H.

        SearchPattern (leb ?a ?b = true -> ?a <= ?b).
        apply leb_complete.
        SearchPattern (?a = ?b -> ?b = ?a).
        apply eq_sym.
        apply Heqb.

      (* else (a > a0) *)
      inversion H.
        (* base part *)
        simpl.
        apply LSorted_consn.
          apply LSorted_cons1.
          SearchPattern (?a < ?b -> ?a <= ?b).
          apply lt_le_weak.
          SearchPattern (leb ?a ?b = false -> _).
          apply leb_complete_conv.
          apply eq_sym.
          apply Heqb.
        (* inductive part *)
        subst.
        simpl.
        simpl in IHl.
        remember (leb a b).
        destruct b0.
          (* case leb a b (a <= b) *)
          apply LSorted_consn.
            apply LSorted_consn.
              apply H2.
              apply leb_complete.
              apply eq_sym.
              apply Heqb0.
            apply lt_le_weak.
            apply leb_complete_conv.
            apply eq_sym.
            apply Heqb.
          (* case else (a > b) *)
          apply LSorted_consn.
            apply IHl.
            apply H2.
            apply H3.
Qed.

Theorem isort_sorted :
  forall (l : list nat),
  LocallySorted le (insertion_sort l)
.
Proof.
  intro l.
  induction l.
    (* base part *)
    simpl.
    SearchPattern (LocallySorted _ nil).
    apply LSorted_nil.
    (* inductive part *)
    simpl.
    apply insert_sorted.
    apply IHl.
Qed. 
