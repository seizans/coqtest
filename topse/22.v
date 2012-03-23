(* lt_dec : forall n m : nat, {n < m} + {~ n < m} *)
Require Import Arith.

Definition max m n := 
  if lt_dec m n then n else m.

Print sumbool.

Theorem max_le :
    forall m n,
    m <= max m n
.
Proof.
  intro m.
  intro n.
  unfold max.
  info destruct lt_dec. 
    SearchPattern (_ < _ -> _ <= _).
    apply lt_le_weak.
    apply l.

    SearchPattern (?n <= ?n).
    apply le_refl.
Qed.


Require Import List.

Definition length_tl :
  forall (A : Type) (xs : list A),
  {n : nat | n = length xs}
.
Proof.
  intro A.
  intro xs.
  Print exist.
  refine (
    let fix iter n ys :=
      match ys with
        | nil => n
        | _ :: ys' => iter (S n) ys'
      end
      in exist _ (iter 0 xs) _
  ).

  assert (Hiter: forall ys n, iter n ys = n + iter 0 ys).
    induction ys; simpl.
      apply plus_n_O.

      intro n.
      rewrite (IHys (S n)).
      rewrite (IHys 1).
      apply plus_n_Sm.

    induction xs.
      simpl.
      reflexivity.

      simpl.
      rewrite <- IHxs.
      apply Hiter.
Qed.



