From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum matrix.
From mathcomp Require Import interval rat.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import functions set_interval mathcomp_extra.
From mathcomp Require Import reals ereal signed topology normedtype landau.
From mathcomp Require Import sequences.

(* Unset Strict Implicit. *)
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section q_tools.
Variable (R : realType) (q : R).
Hypothesis Hq : q - 1 != 0.

Notation "f ** g" := (fun x => f x * g x) (at level 49).
Notation "f // g" := (fun x => f x / g x) (at level 49).
Notation "a */ f" := (fun x => a * (f x)) (at level 49).

(*Definition cvg a b (f : R -> R) := forall e : R, e > 0 -> 
  exists d, (forall x,`|x - a| < d -> `|f x - b| < e).*)

(*Lemma lim_add a b c (f g : R -> R) : cvg a b f -> cvg a c g ->
  cvg a (b + c) (f \+ g).
Proof.
  rewrite /cvg.
  move=> fa_b ga_c e He0.
  move:(fa_b (e/2%:R)) => [].
    apply Num.Theory.divr_gt0 => //.
    by apply Num.Theory.ltr0n.
  move=> d1 fa_b'.
  move:(ga_c (e/2%:R)) => [].
    apply Num.Theory.divr_gt0 => //.
    by apply Num.Theory.ltr0n.
  move=> d2 ga_c'.
  exists (Num.min d1 d2).
  move=> x Hd.
Admitted.*)

(* tools *)
(* 関数の積の交換 *)
Lemma mulfC (f g : R -> R) : f ** g = g ** f.
Proof.
  apply funext => x.
  by rewrite mulrC.
Qed.

(* -の分配則*)
Lemma negdistr (a b : int) : - (a + b) = - a - b.
Proof.
  have -> : - (a + b) = - a + a - (a + b).
    rewrite [- a + a] addrC.
    rewrite -{2}(add0r a) addrK.
    by rewrite sub0r.
  by rewrite addrKA.
Qed.

Lemma Negz_add m n : Negz (m.+1 + n) = Negz m + Negz n.
Proof. by rewrite !NegzE -addnS (negdistr m.+1 n.+1)%N. Qed.

Lemma Negz_addK m n : Negz (m + n) + n = Negz m.
Proof.
  rewrite !NegzE addrC -addn1.
  rewrite (_ : Posz (m + n + 1)%N = Posz m + n + 1) //.
  rewrite -[Posz m + n + 1] addrA.
  rewrite [Posz m + (Posz n + 1)] addrC.
  rewrite -[Posz n + 1 + m] addrA.
  rewrite -{1}(add0r (Posz n)).
  by rewrite addrKA -addn1 sub0r addnC.
Qed.

Lemma NegzK n : Posz n.+1 + Negz n = 0.
Proof. by rewrite NegzE addrN. Qed.

Lemma NegzS n : Negz n.+1 + 1 = Negz n.
Proof. by rewrite -addn1 Negz_addK. Qed.

Lemma opp_oppE (x : R) : - - x = x.
Proof. by rewrite -(sub0r x) (opprB 0) subr0. Qed.

Lemma opp_oppE' (x y : R) : - x * - y = x * y.
Proof. by rewrite mulrN mulNr opp_oppE. Qed.

Lemma eq_int_to_nat (m n : nat): m = n:> int -> m = n.
Proof.
  move=> Hmn.
  have Hmn' : m == n:>int.
    by apply /eqP.
  rewrite -(eqr_int R) Num.Theory.eqr_nat in Hmn'.
  by move/eqP in Hmn'.
Qed.

Lemma mulnon0 (a b : R) : a * b != 0 -> a != 0.
Proof.
  move/eqP.
  case_eq (a == 0) => //.
  move/eqP ->.
  by rewrite mul0r.
Qed.

Lemma expnon0 (x : R) (n : nat) : x != 0 -> x ^ n != 0.
Proof.
  move=> Hx.
  elim: n => [|n IH].
  - by rewrite expr0z oner_neq0.
  - by rewrite exprSz mulf_neq0.
Qed.

Lemma exp_gt1 (x : R) (n : nat) : x > 1 -> x ^ n.+1 > 1.
Proof.
  elim: n => [|n IH] Ix //=.
  rewrite exprSz.
  by apply /Num.Theory.mulr_egt1 /IH.
Qed.

(* Lemma mul_norm (x y : R) : `|x * y| = `|x| * `|y|.
Proof.
  case Hx0 : (x != 0).
  - case Hy0 : (y != 0).
    + case Hx : (0 <= x).
      - case Hy : (0 <= y).
        + rewrite !Num.Theory.ger0_norm //.
          by apply Num.Theory.mulr_ge0.
        + rewrite (@Num.Theory.ger0_norm _ x) //.
          rewrite !Num.Theory.ltr0_norm //.
              by rewrite mulrN.
            by rewrite mc_1_10.Num.Theory.ltrNge Hy.
          rewrite Num.Theory.pmulr_rlt0.
            by rewrite mc_1_10.Num.Theory.ltrNge Hy.
          rewrite  mc_1_10.Num.Theory.ltr_def //.
          by apply /andP; split.
      - case Hy : (0 <= y).
        + rewrite (@Num.Theory.ger0_norm _ y) //.
          rewrite !Num.Theory.ltr0_norm //.
              by rewrite mulNr.
            by rewrite mc_1_10.Num.Theory.ltrNge Hx.
          rewrite Num.Theory.pmulr_llt0.
            by rewrite mc_1_10.Num.Theory.ltrNge Hx.
          rewrite  mc_1_10.Num.Theory.ltr_def //.
          by apply /andP; split.
        + rewrite Num.Theory.ger0_norm.
            rewrite !Num.Theory.ltr0_norm //.
                by rewrite opp_oppE'.
              by rewrite mc_1_10.Num.Theory.ltrNge Hy.
            by rewrite mc_1_10.Num.Theory.ltrNge Hx.
          rewrite mc_1_10.Num.Theory.ltrW // Num.Theory.nmulr_lgt0.
            by rewrite mc_1_10.Num.Theory.ltrNge Hx.
          by rewrite mc_1_10.Num.Theory.ltrNge Hy.
    + move: Hy0.
      move/eqP => ->.
      by rewrite mulr0 !mc_1_10.Num.Theory.normr0 mulr0.
  - move: Hx0.
    move/eqP => ->.
    by rewrite mul0r !mc_1_10.Num.Theory.normr0 mul0r.
Qed. *)

(* Lemma exp_lt1 (x : R) (n : nat) : `|x| < 1 -> `|x ^ n.+1| < 1.
Proof.
  move=> Hx.
  elim: n => [|n IH] //=.
  rewrite exprSz mul_norm.
  by apply Num.Theory.mulr_ilt1.
Qed. *)

(* R上の　add cancel *)
Lemma addrK' (a : R) : a - a = 0.
Proof. by rewrite -{1}(add0r a) addrK. Qed.

(* Rの移項 *)
Lemma rtransposition (a b c : R) : a + b = c -> a = c - b.
Proof. by move=> <-; rewrite addrK. Qed.

(* intの移項 *)
Lemma itransposition (l m n : int) : l + m = n -> l = n - m.
Proof. by move=> <-; rewrite addrK. Qed.


Lemma Negz_transp m n l : m + Negz n = l -> m = l + n.+1.
Proof. rewrite NegzE; apply itransposition. Qed.

(* 両辺にかける *)
Lemma same_prod {a b} (c : R) : c != 0 -> a * c = b * c -> a = b.
Proof.
  move=> Hc.
  by rewrite -{2}(mulr1 a) -{2}(mulr1 b)
     -(@divff _ c) // !mulrA => ->.
Qed.

Lemma denomK (x y : R) : y != 0 ->
  (x / y) * y = x.
Proof.
  move=> Hy.
  by rewrite -mulrA mulVf // mulr1.
Qed.

(* 右側約分 *)
Lemma red_frac_r (x y z : R) : z != 0 ->
  x * z / (y * z) = x / y.
Proof.
  move=> Hz.
  by rewrite -mulf_div divff // mulr1.
Qed.

(* 左側約分 *)
Lemma red_frac_l (x y z : R) : z != 0 ->
  z * x / (z * y) = x / y.
Proof.
  move=> Hz.
  by rewrite [z * x] mulrC [z * y] mulrC red_frac_r.
Qed.

Lemma opp_frac (x y : R) : - x / - y = x / y.
Proof. by rewrite -mulrN1 -(mulrN1 y) red_frac_r //. Qed.

Lemma inv_invE (x : R) : 1 / (1 / x) = x.
Proof. by rewrite divKf // oner_neq0. Qed.

(* 分母共通の和 *)
Lemma add_div (x y z : R) : z != 0 ->
  x / z + y / z = (x + y) / z.
Proof.
  move=> nz0.
  by rewrite addf_div // -mulrDl red_frac_r.
Qed.

(* 頻出分母が0でない *)
Lemma denom_is_nonzero x : x != 0 -> q * x - x != 0.
Proof.
  move=> Hx.
  rewrite -{2}(mul1r x) -mulrBl.
  by apply mulf_neq0.
Qed.

(* Lemma sum_shift m n (F : nat -> R) :
  \sum_(m <= i < n) F i = \sum_(0 <= i < (n - m)) F (i + m)%N.
Proof.
Admitted. *)

Lemma sum_shift m n (F : nat -> R) :
  \sum_(m <= i < m + n.+1) F i = \sum_(0 <= i < n.+1) F (i + m)%N.
Proof.
  elim: n => [|n IH].
  - by rewrite addn1 !big_nat1 add0n.
  - rewrite (@big_cat_nat R _ _ (m + n.+1) m (m + n.+2)) //=.
        rewrite (@big_cat_nat R _ _ n.+1 0 n.+2) //=.
        by rewrite [(m + n.+2)%N] addnS IH !big_nat1 addnC.
      by apply leq_addr.
    by rewrite leq_add2l.
Qed.

Lemma sum_distr n (F : nat -> R) a:
  \sum_(0 <= i < n.+1) F i * a = a * \sum_(0 <= i < n.+1) F i.
Proof.
  elim: n => [|n IH].
  - by rewrite !big_nat1 mulrC.
  - rewrite (@big_cat_nat R _ _ n.+1 0 n.+2) //=.
    rewrite (@big_cat_nat R _ _ n.+1 0 n.+2) //=.
    rewrite !big_nat1 mulrDr IH.
    have -> : F n.+1 * a = a * F n.+1 => //.
    by rewrite mulrC.
Qed.
End q_tools.