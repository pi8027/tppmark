Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq Ssreflect.fintype
  MathComp.path MathComp.fingraph MathComp.bigop MathComp.finset
  MathComp.fingroup MathComp.perm.

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
  [set (b * tperm npos (ex, ey))%g |
    npos : elemt &
    (npos \in [:: (inord ex.-1, ey); (inord ex.+1, ey);
                  (ex, inord ey.-1); (ex, inord ey.+1)]) &&
    (npos != (ex, ey))].

Definition puzzle_reachable : rel board :=
  connect (fun b1 b2 => b2 \in puzzle_next b1).

Definition invariant (b : board) : bool :=
  let (ex, ey) := b^-1%g empty_space in
  ~~ (odd_perm b (+) odd x' (+) odd y' (+) odd ex (+) odd ey).

Lemma invariant1 : invariant 1.
Proof.
  rewrite /invariant invg1 perm1 /empty_space /= odd_perm1 /=.
  by do 2 case: (odd _) => /=.
Qed.

Lemma invariant2 b1 b2 :
  b2 \in puzzle_next b1 -> invariant b1 -> invariant b2.
Proof.
  rewrite /puzzle_next /invariant.
  move: {1 3 4}((b1^-1)%g _) {1 3}((b2^-1)%g _)
    (erefl ((b1^-1)%g empty_space)) (erefl ((b2^-1)%g empty_space)) =>
    /= [] b1x b1y [] b2x b2y Hb1 Hb2.
  case/imsetP => npos; rewrite !inE.
  case/andP; do !case/orP; move/eqP => ?;
    subst npos => H ?; subst b2 => /=; apply contra;
    rewrite odd_permM odd_tperm H /=;
    rewrite eqE /= eqxx ?andbT /= in H.
Abort.

End puzzle.
