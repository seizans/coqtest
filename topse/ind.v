Inductive light : Set :=
  | Blue   : light
  | Yellow : light
  | Red    : light
.


Definition next x :=
  match x with
  | Blue   => Yellow
  | Yellow => Red
  | Red    => Blue
end.


Print nat.

(*
Inductive nat : Set :=
  | O : nat
  | S : nat -> nat
.
*)

Check (S O).

Eval compute in next (next Yellow).


Theorem light_cycles : forall (l : light), next (next (next l)) = l.
Proof.
  intro p.
  destruct p.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

Require Import Arith.

Theorem induction_test' : forall n : nat, n + 0 = n.
Proof.
  intro p.
  rewrite plus_comm.
  simpl.
  reflexivity.
Qed.


Theorem induction_test : forall n : nat, n + 0 = n.
Proof.
  intro p.
  induction p.
    simpl.
    reflexivity.

    simpl.
    rewrite IHp.
    reflexivity.

Qed.







