Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Theorem well_founded_lt : well_founded (fun n m => n < m).
Proof.
  move => x.
  move: {2}x (leqnn x) => n.
  elim: n x => [ | n IHn ] x H; constructor => y H0.
  - apply False_ind, notF.
    rewrite -(ltn0 y).
    apply (leq_trans H0 H).
  - apply IHn.
    rewrite -ltnS.
    apply (leq_trans H0 H).
Defined.

Lemma problem1 a : a ^ 2 %% 3 != 2.
Proof.
  by rewrite /expn /= -modnMm;
    case: (a %% 3) (@ltn_pmod a 3 erefl) => [| [| []]].
Qed.

Lemma problem2 a b c :
  a ^ 2 + b ^ 2 = 3 * c ^ 2 -> [&& 3 %| a, 3 %| b & 3 %| c].
Proof.
  move => H.
  have H0: (3 %| a) && (3 %| b).
    move/(f_equal (modn ^~ 3)):
      H (problem1 a) (problem1 b) (@ltn_pmod a 3 erefl) (@ltn_pmod b 3 erefl).
    rewrite /dvdn /expn /= -modnMml modnn mul0n mod0n -modnDm
            -(modnMm a) -(modnMm b).
    by move: (a %% 3) (b %% 3) => [| [| [| a']]] [| [| []]].
  rewrite andbA H0 /=; move/(f_equal (modn ^~ 9)): H.
  have/eqP {H0} -> : 9 %| a ^ 2 + b ^ 2 by
    rewrite /expn /=; apply dvdn_add; apply (@dvdn_mul 3 3); case/andP: H0.
  move/esym/eqP; rewrite -/(dvdn _ _) (@dvdn_pmul2l 3 3) //.
  rewrite /dvdn /expn /= -modnMm.
  by case: (c %% 3) (@ltn_pmod c 3 erefl) => [| [| []]].
Qed.

Lemma divn_expAC d m n : d %| m -> (m %/ d) ^ n = (m ^ n) %/ (d ^ n).
Proof.
  by move => H; elim: n => //= n IH;
    rewrite !expnS IH divn_mulAC // muln_divA ?dvdn_exp2r // -divnMA (mulnC d).
Qed.

Lemma problem3 a b c :
  a ^ 2 + b ^ 2 = 3 * c ^ 2 -> (a == 0) && (b == 0) && (c == 0).
Proof.
  move => H.
  suff H0: c = 0 by move: H; rewrite H0 exp0n // muln0; move: a b => [] // [].
  move: c (well_founded_lt c) a b H; refine (Acc_ind _ _).
  case => // c _ IH a b H.
  case/and3P: (problem2 H) => H0 H1 H2.
  move: (IH (c.+1 %/ 3)).
  rewrite ltn_Pdiv // => /(_ erefl (a %/ 3) (b %/ 3)).
  rewrite !divn_expAC // -divnDl ?dvdn_mul // H /expn /= muln_divA ?dvdn_mul //.
  move/(_ erefl).
  rewrite -{2}(divnK H2).
  by case: (_ %/ _).
Qed.
