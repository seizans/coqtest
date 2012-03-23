Definition a := 3.

Definition myid (A : Type) (x : A) : A := x.

Definition id' : forall (A : Type), A -> A := fun A x => x.

Eval compute in myid nat 5.
Eval compute in 5.
Eval compute in id' nat 5.


Theorem first_theorem : forall P: Prop, P -> P.
Proof.
  intros P HP.
  apply HP.

Qed.



Theorem x_le_y_tauto : forall (x y: nat), x<y -> x<y.
Proof.
  intros a b.
  apply first_theorem.
Qed.


Theorem p_q_p : forall P Q:Prop, P -> Q -> P.
Proof.
  intro a.
  intro b.
  intro c.
  intro d.
  apply c.
Qed.

Theorem eq2 : forall x a b, (x = a + b) -> (x + 5 = a + b + 5).
Proof.
  intro p.
  intro q.
  intro r.
  intro s.
  rewrite s.
  reflexivity.
Qed.

Require Import Arith List.
Theorem injection_example : forall (a : nat),
    forall (xs : list nat), 1 :: xs = a :: xs -> 1 <= a.
Proof.
  intro p.
  intro q.
  intro r.
  injection r.
  intro s.
  rewrite <- s.
  apply le_refl.
Qed.

Theorem fact5equal120 : fact 5 = 120.
Proof.
  simpl.
  reflexivity.
Qed.
