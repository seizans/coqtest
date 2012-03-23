Inductive list (A : Set) : Set :=
  | Nil : list A
  | Cons : A -> list A -> list A
.

Check Nil.
Check Cons.

Implicit Arguments Nil [A].
Implicit Arguments Cons [A].

Infix "::" := Cons (at level 60, right associativity).

Check (@Nil bool).

Check 3 :: 4 :: Nil.


Fixpoint length  {A : Set} (xs : list A) :=
  match xs with
  | Nil => 0
  | x :: xs' => 1 + length xs'
end.

Definition xs := 3 :: 4 ::1 :: Nil.

Eval compute in length xs.

Fixpoint app {A : Set} (xs ys : list A) :=
  match xs with
  | Nil => ys
  | x :: xs' => x :: app xs' ys
end.

Infix "++" := app (at level 60, right associativity).

Fixpoint rev {A : Set} (xs : list A) :=
  match xs with
  | Nil => Nil
  | x :: xs' => (rev  xs') ++ (x :: Nil)
end.

Eval compute in rev xs.

Fixpoint rev' (A : Set) (xs : list A) :=
  match xs with
  | Nil => Nil
  | x :: xs' => (rev' A xs') ++ (x :: Nil)
  end.

Eval compute in rev' nat xs.

Fixpoint sum (ns : list nat) :=
  match ns with
  | Nil => 0
  | n :: ns' => n + sum ns'
end.

Eval compute in sum xs.

Print Nil.

Definition propo := forall xs, length xs = 0 -> xs = (@Nil nat).
Eval compute in propo.


Theorem app_length : forall {A : Set} (xs ys : list A),
    length (xs ++ ys) = length xs + length ys.
Proof.
  intro A.
  intro xs.
  intro ys.
  induction xs.
    simpl.
    reflexivity.

    simpl.
    rewrite <- IHxs.
    reflexivity.
Qed.

Require Import Arith.

Theorem rev_length : forall {A : Set} (xs : list A),
    length (rev xs) = length xs.
Proof.
  intro A.
  intro xs.
  induction xs.
    simpl.
    reflexivity.

    simpl.
    rewrite app_length.
    simpl.
    rewrite plus_comm.
    rewrite IHxs.
    simpl.
    reflexivity.
Qed.

Theorem app_nil : forall {A : Set} (xs : list A), xs ++ Nil = xs.
Proof.
  intro A.
  intro xs.
  induction xs.
    simpl.
    reflexivity.

    simpl.
    rewrite IHxs.
    reflexivity.
Qed.

Theorem  app_assoc : forall {A : Set} (xs ys zs: list A),
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.
Proof.
  intro A.
  intro xs.
  intro ys.
  intro zs.
  induction xs.
    simpl.
    reflexivity.

    simpl.
    rewrite IHxs.
    reflexivity.
Qed.

Theorem app_rev : forall {A : Set} (xs ys: list A),
    rev (xs ++ ys) = rev ys ++ rev xs.
Proof.
  intro A.
  intro xs.
  intro ys.
  induction xs.
    simpl.
    rewrite app_nil.
    reflexivity.

    simpl.
    rewrite IHxs.
    rewrite app_assoc.
    reflexivity.
Qed.

Theorem rev_rev : forall {A : Set} (xs : list A),
    rev (rev xs) = xs.

  intros A xs.
  induction xs.
    simpl.
    reflexivity.

    simpl.
    rewrite app_rev.
    simpl.
    rewrite IHxs.
    reflexivity.
Qed.


(* 2nd day *)

Require Import Recdef.

Function foo (xs : list nat) {measure length xs} : list nat :=
  match xs with
  | Nil => Nil
  | x :: xs' => x :: foo (rev xs')
  end.

  intro xs.
  intro x.
  intro xs'.
  intro H.
  rewrite rev_length.
  simpl.
  SearchPattern(_ < S _).
  apply lt_n_Sn.
Qed.

