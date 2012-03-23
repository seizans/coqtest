(* Ltac rewrite_reflex H := rewrite in *)

Lemma dup_lemma : forall P, P -> P -> P.
Proof. auto. Qed.

Ltac dupn n :=
  match n with
    | O => idtac
    | S O => idtac
    | S ?n' => apply dup_lemma; [|dupn n']
  end.


Ltac my_tauto :=
  repeat match goal with
  | H: ?P |- ?P => apply H
  | |- True => apply I
  | |- _ /\ _ => split
  | |- _ -> _ => intro
  | H: False |- _ => destruct H
  | H: _ /\ _ |- _ => destruct H
  | H: _ \/ _ |- _ => destruct H
  (* make Q from P -> Q and P *)
  | H1: ?P -> ?Q, H2: ?P |- _ => specialize (H1 H2)
  end.

