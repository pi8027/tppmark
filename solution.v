Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq Ssreflect.fintype
  MathComp.bigop MathComp.finset MathComp.fingroup MathComp.perm.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section puzzle.

Variable (x' y' : nat).
Definition x := x'.+1.
Definition y := y'.+1.

Definition elemt : finType :=
  prod_finType (ordinal_finType x) (ordinal_finType y).
Definition board : baseFinGroupType := perm_of_finGroupType elemt.

Definition empty_space : elemt :=
  (@Ordinal x x.-1 (leqnn x), @Ordinal y y.-1 (leqnn y)).

Definition puzzle_next (b : board) : {set board} :=
  let (ex, ey) := b^-1%g empty_space in
  [set perm_mul b (tperm (ex, ey) npos) |
    npos : elemt &
    (npos \in [:: (inord ex.-1, ey); (inord ex.-1, ey);
                  (ex, inord ey.-1); (ex, inord ey.+1)]) &&
    (npos != (ex, ey))].

(*
Definition puzzle_next' (b : board) : {set board} :=
  let (ex, ey) := b^-1%g empty_space in
  [set perm_mul b (tperm (ex, ey) (ex', ey')) |
    ex' in 'I_x, ey' in 'I_y & odd (ex' + ex) (+) odd (ey' + ey)].
*)

Definition invariant (b : board) : bool :=
  let (ex, ey) := b^-1%g empty_space in
  odd_perm b (+) odd x' (+) odd y' (+) odd ex (+) odd ey.



End puzzle.
