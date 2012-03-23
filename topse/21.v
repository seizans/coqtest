Require Import Streams.
Print Stream.

(* take a look at Standard Library
CoInductive Stream (a : Type) : Type :=
Cons : a -> Stream a -> Stream a
.

CoFixpoint from n := Cons n (from (n+1) ).
*)


Require Import List.

Fixpoint take {a : Type} n (xs : Stream a) :=
  match (n, xs) with
  | (0, _) => nil
  | (S n', Cons x xs) => x :: take n' xs
  end.

CoFixpoint from n := Cons n (from (n + 1) ).

Eval compute in take 10 (from 0).
Eval compute in from 0.

CoFixpoint repeat {a : Type} (x : a) :=
  Cons x (repeat x)
.

Eval compute in take 10 (repeat 3).




