Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq Ssreflect.fintype MathComp.path
  MathComp.fingraph MathComp.finset MathComp.fingroup MathComp.perm.

Definition truncord {m} n : 'I_m.+1 :=
  @Ordinal m.+1 (minn m n) (eq_ind_r _ (geq_minl m n) (ltnS (minn m n) m)).

Definition elemt : finType :=
  prod_finType (ordinal_finType 4) (ordinal_finType 4).
Definition board : baseFinGroupType := perm_of_finGroupType elemt.

Definition empty_space : elemt := (@Ordinal 4 3 erefl, @Ordinal 4 3 erefl).

Definition puzzle_next (b : board) : {set board} :=
  let (ex, ey) := b^-1%g empty_space in
  [set (tperm npos (ex, ey) * b)%g |
    npos : elemt &
    (npos \in [:: (truncord ex.-1, ey); (truncord ex.+1, ey);
                  (ex, truncord ey.-1); (ex, truncord ey.+1)]) &&
    (npos != (ex, ey))].

Definition reachable := connect (fun b1 b2 => b2 \in puzzle_next b1).

Definition invariant (b : board) : bool :=
  let (ex, ey) := b^-1%g empty_space in odd_perm b (+) odd ex (+) odd ey.

Lemma next_invariant b1 b2 :
  b2 \in puzzle_next b1 -> invariant b1 = invariant b2.
Proof.
  rewrite /puzzle_next /invariant.
  by move: {1 3 4}((b1^-1)%g _) (erefl ((b1^-1)%g empty_space)) =>
    /= [b1x b1y] Hb; case/imsetP => npos; rewrite !inE; case/andP; do !case/orP;
    move/eqP => -> H ->; rewrite invMg tpermV permM -{}Hb tpermR odd_mul_tperm;
    move: H; rewrite !eqE /= eqxx 1?andbT /=;
    (move: b1x => [] [| [| [| []]]] //= _ _; [| |]) ||
    (move: b1y => [] [| [| [| []]]] //= _ _; [| |]); case: odd_perm; case: odd.
Qed.

Lemma reachable_invariant b1 b2 :
  reachable b1 b2 -> invariant b1 = invariant b2.
Proof.
  rewrite /reachable; case/connectP => ps H ?; subst b2.
  elim: ps b1 H => //= b2 ps IH b1;
    case/andP; move/next_invariant => ->; apply IH.
Qed.

Theorem tperm_unsolvable :
  ~~ reachable
    (tperm (@Ordinal 4 1 erefl, @Ordinal 4 3 erefl)
           (@Ordinal 4 2 erefl, @Ordinal 4 3 erefl)) 1%g.
Proof.
  apply/negP; move/reachable_invariant; move/eqP; apply/negP.
  by rewrite /invariant tpermV tpermD // odd_tperm invg1 perm1 odd_perm1.
Qed.
