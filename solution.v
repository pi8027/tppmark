Require Import
  Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype
  Ssreflect.ssrnat Ssreflect.seq Ssreflect.fintype
  MathComp.path MathComp.fingraph MathComp.bigop MathComp.finset
  MathComp.fingroup MathComp.perm.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Check @Ordinal.

Definition bind_ord {m} n : 'I_m.+1 :=
  @Ordinal m.+1 (minn m n) (eq_ind_r is_true (geq_minl m n) (ltnS (minn m n) m)).

Lemma bord_minn m n : nat_of_ord (@bind_ord m n) = minn m n.
Proof.
  by rewrite /bind_ord /=.
Qed.

Lemma odd_bord_p m (n : 'I_m.+1) :
  @bind_ord m n.-1 != n -> odd (@bind_ord m n.-1) = ~~ odd n.
Proof.
  by rewrite eqE /=; move: n => [] [] //= n;
    rewrite ltnS; move/ltnW/minn_idPr => ->; case: (odd n).
Qed.

Lemma odd_bord_s m (n : 'I_m.+1) :
  @bind_ord m n.+1 != n -> odd (@bind_ord m n.+1) = ~~ odd n.
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
    (npos \in [:: (bind_ord ex.-1, ey); (bind_ord ex.+1, ey);
                  (ex, bind_ord ey.-1); (ex, bind_ord ey.+1)]) &&
    (npos != (ex, ey))].

Definition puzzle_reachable : rel board :=
  connect (fun b1 b2 => b2 \in puzzle_next b1).

Definition invariant (b : board) : bool :=
  let (ex, ey) := b^-1%g empty_space in
  ~~ (odd_perm b (+) odd ex (+) odd ey (+) odd x' (+) odd y').

Lemma invariant1 : invariant 1.
Proof.
  rewrite /invariant invg1 perm1 /empty_space /= odd_perm1 /=.
  by do 2 case: (odd _) => /=.
Qed.

Lemma invariant2 b1 b2 :
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
    do 3 f_equal; rewrite -2!addbA addNb -addbN; f_equal;
    (rewrite -addNb; f_equal; [] || rewrite -addbN; f_equal; []);
    rewrite ?(odd_bord_p H) ?(odd_bord_s H); case: (odd _).
Qed.

End puzzle.
