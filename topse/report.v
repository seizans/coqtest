Theorem ex1:
  forall x,
  x = 1 -> x + 1 = 2
.
Proof.
  intro x.
  intro p.
  rewrite p.
  reflexivity.
Qed.


Require Import List.

Fixpoint map_succ (ns : list nat) :=
  match ns with
    | nil => nil
    | n :: ns' => (n + 1) :: (map_succ ns')
  end.

Theorem map_succ_keep_length:
  forall (ns : list nat),
  length ns = length (map_succ ns)
.
Proof.
  intro ns.
  induction ns.
    (* base part *)
    simpl.
    reflexivity.

    (* inductive part *)
    simpl.
    rewrite IHns.
    reflexivity.
Qed.
