From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum matrix.
From mathcomp Require Import interval rat.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import functions set_interval mathcomp_extra.
From mathcomp Require Import reals ereal signed topology normedtype landau.
From mathcomp Require Import sequences.
From mathcomp Require Import all_algebra.

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
Lemma negdistr {V : zmodType} (a b : V) : - (a + b) = - a - b.
Proof.
  have -> : - (a + b) = - a + a - (a + b).
    rewrite [- a + a] addrC.
    rewrite -{2}(add0r a) addrK.
    by rewrite sub0r.
  by rewrite addrKA.
Qed.

Lemma halfdistr m n : ~ odd m ->
  ((m + n)./2 = m./2 + n./2)%N.
Proof.
  move=> em.
  rewrite halfD.
  have -> : odd m && odd n = false => //=.
  apply /andP /not_andP.
  by left.
Qed.

Lemma half_add n : (n.+1 + (n.+1 * n)./2 = (n.+2 * (n.+1))./2)%N.
Proof.
  rewrite -{1}(doubleK n.+1) -halfdistr.
    by rewrite -muln2 -mulnDr addnC addn2 mulnC.
  by rewrite odd_double.
Qed.

Lemma Negz_add m n : Negz (m.+1 + n) = Negz m + Negz n.
Proof. by rewrite !NegzE -addnS (negdistr (Posz m.+1) n.+1)%N. Qed.

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
  move /eqP.
  rewrite -(eqr_int R) Num.Theory.eqr_nat.
  by move/eqP.
Qed.

Lemma eq_nat_to_int (m n : nat): m = n -> m = n:> int.
Proof. by move=> ->. Qed.

Lemma eq_nat_to_R (m n : nat) : m = n -> (m = n)%R.
Proof. by move=> ->. Qed.

Lemma mulnon0 (a b : R) : a * b != 0 -> a != 0.
Proof.
  move/eqP.
  case_eq (a == 0) => //.
  move/eqP ->.
  by rewrite mul0r.
Qed.

Lemma mulrC23 {V : comRingType} (a b c d : V) :
  a * b * c * d = a * c * b * d.
Proof.
f_equal.
by rewrite -!mulrA [b * c]mulrC.
Qed.

Lemma exp0rz' n : (GRing.zero R) ^ (Posz n.+1) = 0.
Proof. by rewrite exprSz mul0r. Qed.

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
Lemma addrK' {V : zmodType} (a : V) : a - a = 0.
Proof. by rewrite -{1}(add0r a) addrK. Qed.

(* Rの移項 *)
Lemma rtransposition (a b c : R) : a + b = c -> a = c - b.
Proof. by move=> <-; rewrite addrK. Qed.

(* intの移項 *)
Lemma itransposition (l m n : int) : l + m = n -> l = n - m.
Proof. by move=> <-; rewrite addrK. Qed.


Lemma Negz_transp m n l : m + Negz n = l -> m = l + n.+1.
Proof. rewrite NegzE; apply itransposition. Qed.

Lemma same_addl {V : zmodType} {a b} (c : V) : c + a = c + b -> a = b.
Proof.
  move=> H.
  rewrite -(addr0 a) -(addrK' c) addrA [a + c] addrC H.
  by rewrite [c + b] addrC -addrA addrK' addr0.
Qed.

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

Lemma denom_comm (x y z : R) : x / y / z = x / z / y.
Proof. by rewrite -mulrA [y^-1 / z] mulrC mulrA. Qed.

Lemma sumW {V : zmodType} n (F : nat -> V) :
  \sum_(i < n) F i = \sum_(0 <= i < n) F i.
Proof. by rewrite big_mkord. Qed.

(* Lemma sum_shift m n (F : nat -> R) :
  \sum_(m <= i < m + n.+1) F i = \sum_(0 <= i < n.+1) F (i + m)%N.
Proof.
  elim: n => [|n IH].
  - by rewrite addn1 !big_nat1 add0n.
  - rewrite (@big_cat_nat R _ _ (m + n.+1) m (m + n.+2)) //=.
        rewrite (@big_cat_nat R _ _ n.+1 0 n.+2) //=.
        by rewrite [(m + n.+2)%N] addnS IH !big_nat1 addnC.
      by apply leq_addr.
    by rewrite leq_add2l.
Qed. *)

Lemma sum_add {V : zmodType} n (F G : nat -> V) :
  \sum_(0 <= i < n) (F i) + \sum_(0 <= i < n) (G i) =
  \sum_(0 <= i < n) (F i + G i).
Proof.
  elim: n => [|n IH].
  - by rewrite !big_nil addr0.
  - rewrite !(@big_cat_nat _ _ _ n 0 n.+1) //= !big_nat1.
    rewrite -IH -!addrA.
    congr (_ + _).
    by rewrite addrC -addrA [G n + F n]addrC.
Qed.

Lemma sum_sub {V : zmodType} n (F G : nat -> V) :
  \sum_(0 <= i < n) (F i) - \sum_(0 <= i < n) (G i) =
  \sum_(0 <= i < n) (F i - G i).
Proof.
  elim: n => [|n IH].
  - by rewrite !big_nil subr0.
  - rewrite !(@big_cat_nat _ _ _ n 0 n.+1) //= !big_nat1.
    rewrite -IH -!addrA.
    congr (_ + _).
    by rewrite addrC addrA negdistr -addrA [- G n + F n]addrC addrA.
Qed.

Lemma sum_distr {V : comRingType} n (F : nat -> V) (a : V) :
  \sum_(0 <= i < n) (F i * a) = a * \sum_(0 <= i < n) F i.
Proof.
  elim: n => [|n IH].
  - by rewrite !big_nil mulr0.
  - rewrite !(@big_cat_nat _ _ _ n 0 n.+1) //=.
    by rewrite !big_nat1 mulrDr IH [F n * a]mulrC.
Qed.

Lemma sum n : (2 * (\sum_(0 <= i < n.+1) Posz i) = Posz n * n.+1)%R.
Proof.
  elim:n => [|n IH].
  - by rewrite big_nat1 mulr0 mul0r.
  - rewrite !(@big_cat_nat _ _ _ n.+1 0 n.+2) //= mulrDr IH.
    rewrite big_nat1.
    rewrite -(mulrDl _ _ (Posz n.+1)) mulrC.
    have -> : Posz n + 2 = n.+2 => //.
    apply eq_nat_to_int.
    by rewrite addn2.
Qed.

Lemma sum_poly_div n F (P : nat -> {poly R}) C x :
  \sum_(0 <= i < n.+1) (F i * (P i).[x] / C i) =
  \sum_(0 <= i < n.+1) (F i * (P i / (C i)%:P).[x]) .
Proof.
  elim: n => [|n IH].
  - by rewrite !big_nat1 hornerM polyCV hornerC mulrA.
  - rewrite !(@big_cat_nat _ _ _ n.+1 0 n.+2) //= IH.
    by rewrite !big_nat1 hornerM polyCV hornerC mulrA.
Qed.

Lemma divpsum n P (d : {poly R}) :
  (\sum_(0 <= i < n) P i) %/ d = \sum_(0 <= i < n) (P i %/ d).
Proof.
elim: n => [|n IH].
- by rewrite !big_nil div0p.
- by rewrite !(@big_cat_nat _ _ _ n 0 n.+1) //= !big_nat1 divpD IH.
Qed.

Lemma polyW (p : {poly R}) n (a : nat -> R) : ((size p) <= n)%N ->
  \poly_(i < size p) (a i * p`_i.+1) =
  \sum_(0 <= i < n) (a i * p`_i.+1) *: 'X^i.
Proof.
  move=> H.
  rewrite poly_def.
  rewrite (@big_cat_nat _ _ _ (size p)) //= big_mkord big_nat -[LHS]addr0.
  congr (_ + _).
  rewrite big1 // => i /andP [Hi _].
  move/leq_sizeP : Hi -> => //.
  by rewrite mulr0 scale0r.
Qed.

Lemma polyW' (p : {poly R}) n (a : nat -> R) : ((size p) <= n)%N ->
  \poly_(i < size p) (a i * p`_i) =
  \sum_(0 <= i < n) (a i * p`_i) *: 'X^i.
Proof.
  move=> H.
  rewrite poly_def.
  rewrite (@big_cat_nat _ _ _ (size p)) //= big_mkord big_nat -[LHS]addr0.
  congr (_ + _).
  rewrite big1 // => i /andP [Hi _].
  move/leq_sizeP : Hi -> => //.
  by rewrite mulr0 scale0r.
Qed.

Lemma size_N0_lt (p : {poly R}) : (size p == 0%N) = false -> (0 < size p)%N.
Proof.
move=> Hsize.
rewrite ltn_neqAle.
apply /andP; split => //.
move: Hsize.
by rewrite eq_sym => ->.
Qed.

(* not used *)

(*Lemma qpoly_ex a (n : nat) x : qpoly a (- 1) x = 1 / (x - q ^ (- 1) * a) .
Proof.
  move=> /=.
  rewrite /qpoly_neg /=.
  rewrite expr0z !mul1r.
  rewrite (_ : Negz 1 + 1 = - 1) //.
Qed.*)

(* Lemma sum_onefderiv_pos j n c D P : islinear D -> isfderiv D P ->
  (j <= n)%N -> 
  \sum_(j.+1 <= i < n.+1) c i *: D (P (i - j)%N) =
  \sum_(j.+1 <= i < n.+1) c i *: P (i - j.+1)%N.
Proof.
  move=> HlD Hd Hjn.
  under eq_big_nat => i /andP [Hi HI'].
    have -> : (i - j)%N = (i - j.+1)%N.+1.
      by rewrite subnS prednK // subn_gt0.
    rewrite (Hd (i - j.+1).+1).
  over. done.
Qed. *)

(* Lemma sum_fderiv_pos j n D P c : islinear D -> isfderiv D P ->
  (j <= n)%N ->
  \sum_(j <= i < n.+1) c i *: (D \^ j) (P i) =
  \sum_(j <= i < n.+1) c i *: P (i - j)%N.
Proof.
  move=> HlD Hd.
  elim:j => [|j IH] Hjn.
  - elim: n Hjn => [|n IH'] Hjn.
    + by rewrite !big_nat1 subn0.
    + rewrite (@big_cat_nat _ _ _ n.+1) //= big_nat1 IH' //.
      by rewrite [RHS] (@big_cat_nat _ _ _ n.+1) //= big_nat1 subn0.
  - have Hjn' : (j < n.+1)%N.
      by apply leqW.
    move: (IH (ltnW Hjn)).
    rewrite (@big_cat_nat _ _ _ j.+1) //= big_nat1.
    rewrite nthisfderiv_pos // subnn.
    rewrite (@big_cat_nat _ _ _ j.+1 j) //= big_nat1 subnn.
    move /(same_addl (c j *: P 0%N)) => IH'.
    rewrite -linear_distr' // IH' linear_distr' //.
    by apply sum_onefderiv_pos.
Qed. *)

(* Lemma sum_isfderiv_0 n c D (P : nat -> {poly R}) :
  islinear D -> isfderiv D P ->
  \sum_(0 <= i < n.+1) c i *: (D \^ n.+1) (P i) = 0.
Proof.
  elim: n => [/= |n IH] HlD Hd.
  - rewrite big_nat1.
    have -> : D (P 0%N) = 0.
      by apply (Hd 0%N).
    by rewrite scaler0.
  - rewrite (@big_cat_nat _ _ _ n.+1) //.
    rewrite big_nat1 (lock n.+1) /= -lock.
    rewrite -linear_distr // IH //.
    rewrite linear0 // add0r.
    rewrite nthisfderiv_pos // subnn.
    have -> : D (P 0%N) = 0.
      by apply (Hd 0%N).
    by rewrite scaler0.
Qed. *)

End q_tools.