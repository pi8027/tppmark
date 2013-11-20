Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq Ssreflect.fintype MathComp.path
  MathComp.fingraph MathComp.finset MathComp.fingroup MathComp.perm.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition truncord {m} n : 'I_m.+1 :=
  @Ordinal m.+1 (minn m n) (eq_ind_r _ (geq_minl m n) (ltnS (minn m n) m)).

Lemma odd_tord_p m (n : 'I_m.+1) :
  @truncord m n.-1 != n -> odd (@truncord m n.-1) = ~~ odd n.
Proof.
  by rewrite eqE /=; move: n => [] [] //= n;
    rewrite ltnS; move/ltnW/minn_idPr => ->; case: (odd n).
Qed.

Lemma odd_tord_s m (n : 'I_m.+1) :
  @truncord m n.+1 != n -> odd (@truncord m n.+1) = ~~ odd n.
Proof.
  rewrite eqE /=; case: n => /= n; rewrite ltnS leq_eqVlt; case/orP.
  - by move/eqP => ?; subst n; rewrite (minn_idPl (leqnSn m)) eqxx.
  - by move/minn_idPr => ->.
Qed.

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
  [set (tperm npos (ex, ey) * b)%g |
    npos : elemt &
    (npos \in [:: (truncord ex.-1, ey); (truncord ex.+1, ey);
                  (ex, truncord ey.-1); (ex, truncord ey.+1)]) &&
    (npos != (ex, ey))].

Definition reachable := connect (fun b1 b2 => b2 \in puzzle_next b1).

Definition invariant (b : board) : bool :=
  let (ex, ey) := b^-1%g empty_space in
  odd_perm b (+) odd ex (+) odd ey (+) odd x (+) odd y.

Lemma next_invariant b1 b2 :
  b2 \in puzzle_next b1 -> invariant b1 = invariant b2.
Proof.
  rewrite /puzzle_next /invariant.
  move: {1 3 4}((b1^-1)%g _) {1 3}((b2^-1)%g _)
    (erefl ((b1^-1)%g empty_space)) (erefl ((b2^-1)%g empty_space)) =>
    /= [] b1x b1y [] b2x b2y Hb1 Hb2.
  case/imsetP => npos; rewrite !inE.
  by case/andP; do !case/orP; move/eqP => ? H ?; subst npos b2 => /=;
    move: Hb2; rewrite odd_mul_tperm H /= invMg tpermV permM -{}Hb1 tpermR;
    move/eqP; move: H; rewrite !eqE /= eqxx 1?andbT /= => H;
    case/andP; move/eqP => ?; move/eqP => ?; subst b2x b2y;
    do 2 f_equal; rewrite -2!addbA addNb -addbN; f_equal;
    (rewrite -addNb; f_equal; [] || rewrite -addbN; f_equal; []);
    rewrite ?(odd_tord_p H) ?(odd_tord_s H); case: (odd _).
Qed.

Lemma reachable_cond b1 b2 : reachable b1 b2 -> invariant b1 = invariant b2.
Proof.
  rewrite /reachable; case/connectP => ps H ?; subst b2.
  elim: ps b1 H => //= b2 ps IH b1; case/andP; move/next_invariant => ->.
  apply IH.
Qed.

Theorem tperm_unsolvable e1 e2 : e1 != e2 ->
  e1 != empty_space -> e2 != empty_space -> ~~ reachable (tperm e1 e2) 1%g.
Proof.
  move => H H0 H1; apply/negP; move/reachable_cond; move/eqP; apply/negP.
  by rewrite /invariant tpermV tpermD //
             odd_tperm H invg1 perm1 odd_perm1 /= !addNb; case: (_ (+) _).
Qed.

End puzzle.

Check (@tperm_unsolvable 3 3
  (@Ordinal 4 1 erefl, @Ordinal 4 3 erefl)
  (@Ordinal 4 2 erefl, @Ordinal 4 3 erefl) erefl erefl erefl).
