Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq Ssreflect.fintype Ssreflect.tuple.

Set Implicit Arguments.

Section puzzle.

Variable (x y : nat) (Hx : 0 < x) (Hy : 0 < y).

Definition elemt : finType := ordinal_finType (x * y).

Lemma board_is_nonempty : (x * y).-1 < (x * y).
Proof.
  have: (0 < x * y) by rewrite muln_gt0 Hx Hy.
  by case: (x * y).
Qed.

Definition empty_space : elemt :=
  @Ordinal (x * y) (x * y).-1 board_is_nonempty.

Record board := Board {
  bbody : 'I_x -> 'I_y -> elemt;
  _ : forall x1 x2 y1 y2, x1 <> x2 \/ y1 <> y2 -> bbody x1 y1 <> bbody x2 y2
  }.

(*
another definition:

Record board := Board {
  bbody : y.-tuple(x.-tuple(elemt));
  _ : forall x, count (@pred1 elemt x) (flatten (map (@tval _ _) bbody)) = 1
  }.
*)



End puzzle.
