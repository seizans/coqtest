Lemma solving_by_reflexivity:
    2 + 3 = 5
.
Proof.
  simpl.
  reflexivity.
Qed.

Lemma solving_by_apply :
  forall (P Q: nat -> Prop),
  (forall n, Q n -> P n)
  -> (forall n, Q n)
  -> P 2.
Proof.
  intros P Q n1 n2.
  apply n1.
  apply n2.
Qed.

Lemma solving_conj_goal:
  forall (P: nat -> Prop) (F: Prop),
  (forall n, P n) -> F -> F /\ P 2.
Proof.
  auto.
Qed.

Require Import Arith.
(* add Le.le_refl to hint database *)
Hint Resolve Le.le_refl.
(* add molt_le_compat_l to arith database. *)
Hint Resolve mult_le_compat_l: arith.


Require Import Omega.

Lemma omega_demo :
  forall (x y z : nat),
  (x + y = z + z) -> (x - y <= 4) -> (x - z <= 2)
.
Proof.
  intros.
  info omega.
Qed.

Lemma omega_demo' :
  forall (x y : nat),
  (x + 5 <= y) -> (y - x < 3) -> False
.
Proof.
  intros.
  info omega.
Qed.


Require Import ZArith.
Open Scope Z_scope.

Lemma ring_demo:
  forall (x y z: Z),
  x * (y + z) - z * 3 * x = x * y - 2 * x * z
.
Proof.
  intros.
  info ring.
Qed.


Open Scope nat_scope.

Lemma congruence_demo :
  forall (f : nat -> nat -> nat),
  forall (g h : nat -> nat),
  forall (x y z : nat),
  (forall a, g a = h a)
  -> f (g x) (g y) = z
  -> g x = 2
  -> f 2 (h y) = z
.
Proof.
  intros.
  info rewrite <- H1.
  rewrite <-  H.
  apply H0.
  (* congruence. *)
Qed.

Lemma congruence_demo':
  forall (f g : nat -> nat),
  (forall a, f a = g a) -> f (g (g 2) ) = g (f (f 2) )
.
Proof.
  intros.

  info congruence.
Qed.


