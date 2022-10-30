(* From mathcomp Require Import all_ssreflect all_algebra.
Import GRing.
(*Import Numtheory.*)
(* algebra の中の　ssrnum *)
(* Unset Printing Notations.*)

(* Num.Theory.nmulrn_rle0 *)
(* apply Num.Theory.ltr_normlW. `|x| < y -> x < y*)
Axiom funext : forall A B (f g : A -> B), f =1 g -> f = g.*)

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

Section q_analogue.
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

(* main *)
(* q-differential *)
Definition dq (f : R -> R) x := f (q * x) - f x.

(* q-differential product rule *)
Lemma dq_prod f g x :
  dq (f ** g) x = (f (q * x)) * dq g x + (g x) * dq f x.
Proof.
  rewrite /dq !mulrBr.
  rewrite [in g x * f (q * x)] mulrC.
  by rewrite [in g x * f x] mulrC subrKA.
Qed.

(* q-derivative *)
Definition Dq f := dq f // dq id.

(* q-derivative for const is 0 *)
Lemma Dq_const x c : Dq (fun x => c) x = 0.
Proof. by rewrite /Dq /dq addrK' mul0r. Qed.

(* q-derivative is linear *)
Lemma Dq_is_linear f g a b x :
  x != 0 -> Dq ((a */ f) \+ (b */ g)) x = a * (Dq f x) + b * (Dq g x).
Proof.
  move=> Hx.
  rewrite /Dq /dq !mulrA add_div.
    rewrite !mulrBr opprD !addrA.
    rewrite [a * f (q * x) + b * g (q * x) - a * f x]
              addrC.
    rewrite [(a * f (q * x) + b * g (q * x))]
              addrC.
    rewrite addrA.
    rewrite [- (a * f x) + b * g (q * x) + a * f (q * x)]
            addrC.
    by rewrite addrA.
  by apply denom_is_nonzero.
Qed.

(* q-analogue of natural number *)
Definition q_nat n : R := (q ^ n - 1) / (q - 1).

(* q_nat 0 is 0 *)
Lemma q_nat_0 : q_nat 0 = 0.
Proof. by rewrite /q_nat expr0z addrK' mul0r. Qed.

Lemma q_nat1 : q_nat 1 = 1.
Proof. by rewrite /q_nat expr1z divff. Qed.

Lemma q_natE (n : nat) : q_nat n.+1 = \sum_(0 <= i < n.+1) (q ^ i).
Proof.
  elim: n => [|n IH].
  - by rewrite q_nat1 big_nat1 expr0z.
  - have -> : q_nat n.+2 = q_nat n.+1 + q ^ n.+1.
      apply (same_prod (q - 1)) => //.
      by rewrite mulrDl !denomK // mulrBr mulr1 -exprSzr
                [RHS] addrC subrKA.
    rewrite IH.
    rewrite [RHS] (@big_cat_nat _ _ _ n.+1) //=.
    by rewrite big_nat1.
Qed.

Lemma q_nat_cat {n} j : (j < n)%N ->
  q_nat n.+1 = q_nat j.+1 + q ^ j.+1 * q_nat (n.+1 - j.+1)%N .
Proof.
  move=> Hjn.
  have Hjn' : (j < n.+1)%N.
    by apply (@ltn_trans n).
  have Hjn'' : (0 < n.+1 - j.+1)%N.
    rewrite subn_gt0.
    have -> : j.+1 = (j + 1)%N. by rewrite -addn1.
    have -> : n.+1 = (n + 1)%N. by rewrite -addn1.
    by rewrite ltn_add2r.
  rewrite !q_natE.
  rewrite (@big_cat_nat _ _ _ j.+1) //=.
  have -> : n.+1 = (j.+1 + (n.+1 - j.+1 - 1).+1)%N.
    by rewrite addnS addnBA // subnKC // -{2}addn1 addnK.
  rewrite (sum_shift j.+1).
  have -> : (j.+1 + (n.+1 - j.+1 - 1).+1 - j.+1)%N =
            (n.+1 - j.+1 - 1).+1.
    by rewrite addnC addnK.
  have H : forall m l, \sum_(0 <= i < m.+1) q ^ (i + l)%N =
                       \sum_(0 <= i < m.+1) q ^ i * q ^ l.
    move=> m l.
    elim: m => [|m IH].
    - by rewrite !big_nat1 {1}exprzD_nat.
    - rewrite (@big_cat_nat _ _ _ m.+1) //=.
      rewrite [RHS] (@big_cat_nat _ _ _ m.+1) //=.
      by rewrite !big_nat1 !IH exprzD_nat.
  by rewrite H sum_distr q_natE.
Qed.

(* Lemma q_nat_ispos n : -1 < q -> q_nat n.+1 > 0.
Proof.
  move=> Hq1.
  rewrite /q_nat.
  case H : (q - 1 >= 0).
  - have H' : 0 < q - 1.
      rewrite Num.Theory.lt0r.
      by apply /andP.
    apply Num.Theory.divr_gt0 => //.
    rewrite Num.Theory.subr_gt0.
    apply exp_gt1.
    by rewrite -Num.Theory.subr_gt0.
  - have H' : (0 < 1 - q).
      by rewrite -opprB Num.Theory.oppr_gt0
              mc_1_10.Num.Theory.ltrNge H.
    rewrite -opp_frac !opprB.
    apply Num.Theory.divr_gt0 => //.
    rewrite Num.Theory.subr_gt0.
    apply /Num.Theory.ltr_normlW /exp_lt1.
    rewrite Num.Theory.ltr_norml.
    apply /andP; split => //.
    by rewrite -Num.Theory.subr_gt0.
Qed. *)

(* Lemma q_nat_non0 n : q_nat n.+1 != 0.
Proof. by apply /Num.Theory.lt0r_neq0 /q_nat_ispos. Qed. *)

(*Lemma prod_qpoly_nonneg a n x :
  qpoly_nonneg a n.+1 x = \prod_(0 <= i < n.+1) (x -  q ^ i * a).
Proof.
  elim: n => [/=|n IH].
  - by rewrite big_nat1 mul1r.
  - rewrite (@big_cat_nat _ _ _ n.+1) //=.
    by rewrite big_nat1 -IH.
Qed.*)
Lemma lim_q_nat n : forall e : R, e > 0 ->
  exists d, `|q - 1| < d -> `|n%:R - (q_nat n)| < e.
Proof.
  move=> e He.
  destruct n.
  - eexists => _.
    by rewrite q_nat_0 addrK' Num.Theory.normr0.
  - exists (e / n%:R).
Admitted.

(* q-derivative of x ^ n *)
Lemma qderiv_of_pow n x :
  x != 0 -> Dq (fun x => x ^ n) x = q_nat n * x ^ (n - 1).
Proof.
  move=> Hx.
  rewrite /Dq /dq /q_nat.
  rewrite -{4}(mul1r x) -mulrBl expfzMl.
    rewrite -add_div.
    rewrite [in x ^ n](_ : n = (n -1) +1) //.
      rewrite expfzDr // expr1z.
      rewrite mulrA -mulNr !red_frac_r //.
      rewrite add_div //.
      rewrite -{2}[x ^ (n - 1)]mul1r.
      rewrite -mulrBl mulrC mulrA.
      by rewrite [in (q - 1)^-1 * (q ^ n - 1)] mulrC.
    by rewrite subrK.
  by apply mulf_neq0.
Qed.

(* q-derivative product rule *)
Lemma qderiv_prod f g x : x != 0 ->
  Dq (f ** g) x = f (q * x) * Dq g x + (g x) * Dq f x.
Proof.
  move=> Hx.
  rewrite /Dq dq_prod -add_div.
    by rewrite !mulrA.
  by apply denom_is_nonzero.
Qed.

(* q-derivative product rule' *)
Lemma qderiv_prod' f g x : x != 0 ->
   Dq (f ** g) x = (f x) * Dq g x + g (q * x) * Dq f x.
Proof.
  move=> Hx.
  by rewrite mulfC qderiv_prod // addrC.
Qed.

(* reduce fraction in q-derivative *)
Lemma qderiv_divff f g x : g x != 0 -> g (q * x) != 0 ->
  Dq (g ** (f // g)) x = Dq f x.
Proof.
  move=> Hgx Hgqx.
  rewrite /Dq /dq.
  rewrite [f (q * x) / g (q * x)] mulrC.
  rewrite [f x / g x] mulrC.
  by rewrite !mulrA !divff // !mul1r.
Qed.

(* q-derivative quotient rule *)
Lemma qderiv_quot f g x : x != 0 -> g x != 0 -> g (q * x) != 0 ->
  Dq (f // g) x =
  (g x * Dq f x - f x * Dq g x) / (g x * g (q * x)).
Proof.
  move=> Hx Hgx Hgqx.
  rewrite -add_div.
    rewrite red_frac_l // mulNr.
    apply /rtransposition /(same_prod (g (q * x))) => //.
    rewrite mulrDl.
    rewrite -[f x * Dq g x / (g x * g (q * x)) * g (q * x)]
              mulrA.
    rewrite [(g x * g (q * x))^-1 * g (q * x)] mulrC.
    rewrite mulrA red_frac_r //.
    rewrite -[Dq f x / g (q * x) * g (q * x)] mulrA.
    rewrite [(g (q * x))^-1 * g (q * x)] mulrC.
    rewrite divff // mulr1 mulrC.
    rewrite -[f x * Dq g x / g x] mulrA.
    rewrite [Dq g x / g x] mulrC.
    rewrite [f x * ((g x)^-1 * Dq g x)] mulrA.
    rewrite -qderiv_prod //.
    by apply qderiv_divff.
  by apply mulf_neq0.
Qed.

(* q-derivative quotient rule' *)
Lemma qderiv_quot' f g x : x != 0 ->
  g x != 0 -> g (q * x) != 0 ->
  Dq (f // g) x =
  (g (q * x) * Dq f x
   - f (q * x) * Dq g x) / (g x * g (q * x)).
Proof.
  move=> Hx Hgx Hgqx.
  rewrite -add_div.
    rewrite [g x * g (q * x)] mulrC.
    rewrite red_frac_l // mulNr.
    apply /rtransposition /(same_prod (g x)) => //.
    rewrite mulrDl.
    rewrite [f (q * x) * Dq g x / (g (q * x) * g x) * g x]
              mulrC.
    rewrite [g (q * x) * g x] mulrC.
    rewrite mulrA red_frac_l //.
    rewrite -[Dq f x / g x * g x] mulrA.
    rewrite [(g x)^-1 * g x] mulrC.
    rewrite divff // mulr1 mulrC.
    rewrite -[f (q * x) * Dq g x / g (q * x)] mulrA.
    rewrite [Dq g x / g (q * x)] mulrC.
    rewrite [f (q * x) * ((g (q * x))^-1 * Dq g x)] mulrA.
    rewrite -qderiv_prod' //.
    by apply qderiv_divff.
  by apply mulf_neq0.
Qed.

(* q-analogue of polynomial for nat *)
Fixpoint qpoly_nonneg a n x :=
  match n with
  | 0 => 1
  | n.+1 => (qpoly_nonneg a n x) * (x - q ^ n * a)
  end.

Lemma qpoly_nonneg_head a n x:
   qpoly_nonneg a n.+1 x =
  (x - a) * qpoly_nonneg (q * a) n x.
Proof.
  elim: n => [|n IH] /=.
  - by rewrite expr0z !mul1r mulr1.
  - by rewrite !mulrA -IH exprSzr.
Qed.

(*Lemma prod_qpoly_nonneg a n x :
  qpoly_nonneg a n.+1 x = \prod_(0 <= i < n.+1) (x -  q ^ i * a).
Proof.
  elim: n => [/=|n IH].
  - by rewrite big_nat1 mul1r.
  - rewrite (@big_cat_nat _ _ _ n.+1) //=.
    by rewrite big_nat1 -IH.
Qed.*)

(* q-derivative of q-polynomial for nat *)
Theorem qderiv_qpoly_nonneg a n x : x != 0 ->
  Dq (qpoly_nonneg a n.+1) x =
  q_nat n.+1 * qpoly_nonneg a n x.
Proof.
  move=> Hx.
  elim: n => [|n IH].
  - rewrite /Dq /dq /qpoly_nonneg /q_nat.
    rewrite !mul1r mulr1 expr1z.
    rewrite opprB subrKA !divff //.
    by rewrite denom_is_nonzero.
  - rewrite (_ : Dq (qpoly_nonneg a n.+2) x =
                 Dq ((qpoly_nonneg a n.+1) **
                 (fun x => (x - q ^ (n.+1) * a))) x) //.
    rewrite qderiv_prod' //.
    rewrite [Dq (+%R^~ (- (q ^ n.+1 * a))) x] /Dq /dq.
    rewrite opprB subrKA divff //.
      rewrite mulr1 exprSz.
      rewrite -[q * q ^ n * a] mulrA -(mulrBr q) IH.
      rewrite -[q * (x - q ^ n * a) * (q_nat n.+1 * qpoly_nonneg a n x)] mulrA.
      rewrite [(x - q ^ n * a) * (q_nat n.+1 * qpoly_nonneg a n x)] mulrC.
      rewrite -[q_nat n.+1 * qpoly_nonneg a n x * (x - q ^ n * a)] mulrA.
      rewrite (_ : qpoly_nonneg a n x * (x - q ^ n * a) = qpoly_nonneg a n.+1 x) //.
      rewrite mulrA.
      rewrite -{1}(mul1r (qpoly_nonneg a n.+1 x)).
      rewrite -mulrDl addrC.
      rewrite -(@divff _ (q - 1)) //.
      rewrite [q_nat n.+1] /q_nat.
      rewrite [q * ((q ^ n.+1 - 1) / (q - 1))] mulrA.
      rewrite (add_div _ _ (q - 1)) //.
      by rewrite mulrBr -exprSz mulr1 subrKA.
    by apply denom_is_nonzero.
Qed.

(* q-polynomial exponential law for nat *)
Lemma qpoly_nonneg_explaw x a m n :
  qpoly_nonneg a (m + n) x =
    qpoly_nonneg a m x * qpoly_nonneg (q ^ m * a) n x.
Proof.
  elim: n.
  - by rewrite addn0 /= mulr1.
  - elim => [_|n _ IH].
    + by rewrite addnS /= addn0 expr0z !mul1r.
    + rewrite addnS [LHS]/= IH /= !mulrA.
      by rewrite -[q ^ n.+1 * q ^ m] expfz_n0addr // addnC.
Qed.

Lemma qpoly_exp_non0l x a m n :
  qpoly_nonneg a (m + n) x != 0 -> qpoly_nonneg a m x != 0.
Proof.
  rewrite qpoly_nonneg_explaw.
  by apply mulnon0.
Qed.

Lemma qpoly_exp_non0r x a m n :
  qpoly_nonneg a (m + n) x != 0 -> qpoly_nonneg (q ^ m * a) n x != 0.
Proof.
  rewrite qpoly_nonneg_explaw mulrC.
  by apply mulnon0.
Qed.

(* q-polynomial for neg *)
Definition qpoly_neg a n x := 1 / qpoly_nonneg (q ^ ((Negz n) + 1) * a) n x.

(* q-poly_nat 0 = q-poly_neg 0 *)
Lemma qpoly_0 a x : qpoly_neg a 0 x = qpoly_nonneg a 0 x.
Proof.
  by rewrite /qpoly_neg /= -[RHS] (@divff _ 1) //.
Qed.

Theorem qpoly_neg_inv a n x :
  qpoly_nonneg (q ^ (Negz n + 1) * a) n x != 0 ->
  qpoly_neg a n x * qpoly_nonneg (q ^ (Negz n + 1) * a) n x = 1.
Proof.
  move=> H.
  by rewrite /qpoly_neg mulrC mulrA mulr1 divff.
Qed.

(* q-analogue polynomial for int *)
Definition qpoly a n x :=
  match n with
  | Posz n0 => qpoly_nonneg a n0 x
  | Negz n0 => qpoly_neg a n0.+1 x
  end.

Definition qpoly_denom a n x := match n with
  | Posz n0 => 1
  | Negz n0 => qpoly_nonneg (q ^ Negz n0 * a) n0.+1 x
  end.

Lemma Dq_qpoly_int_to_neg a n x :
  Dq (qpoly a (Negz n)) x = Dq (qpoly_neg a (n + 1)) x.
Proof. by rewrite /Dq /dq /= addn1. Qed.

(*Lemma qpoly_ex a (n : nat) x : qpoly a (- 1) x = 1 / (x - q ^ (- 1) * a) .
Proof.
  move=> /=.
  rewrite /qpoly_neg /=.
  rewrite expr0z !mul1r.
  rewrite (_ : Negz 1 + 1 = - 1) //.
Qed.*)

Lemma qpoly_exp_0 a m n x : m = 0 \/ n = 0 ->
  qpoly a (m + n) x = qpoly a m x * qpoly (q ^ m * a) n x.
Proof.
  move=> [->|->].
  - by rewrite add0r expr0z /= !mul1r.
  - by rewrite addr0 /= mulr1.
Qed.

Lemma qpoly_exp_pos_neg a (m n : nat) x : q != 0 ->
  qpoly_nonneg (q ^ (Posz m + Negz n) * a) n.+1 x != 0 ->
  qpoly a (Posz m + Negz n) x = qpoly a m x * qpoly (q ^ m * a) (Negz n) x.
Proof.
  move=> Hq0 Hqpolymn.
  case Hmn : (Posz m + Negz n) => [l|l]  /=.
  - rewrite /qpoly_neg mul1r.
    rewrite (_ : qpoly_nonneg a m x = qpoly_nonneg a (l + n.+1) x).
      rewrite qpoly_nonneg_explaw.
      have -> : q ^ (Negz n.+1 + 1) * (q ^ m * a) = q ^ l * a.
        by rewrite mulrA -expfzDr // -addn1 Negz_addK addrC Hmn.
      rewrite -{2}(mul1r (qpoly_nonneg (q ^ l * a) n.+1 x)).
      rewrite red_frac_r.
        by rewrite divr1.
      by rewrite -Hmn.
    apply Negz_transp in Hmn.
    apply eq_int_to_nat in Hmn.
    by rewrite Hmn.
  - rewrite /qpoly_neg.
    have Hmn' : n.+1 = (l.+1 + m)%N.
      move /Negz_transp /esym in Hmn.
      rewrite addrC in Hmn.
      move /Negz_transp /eq_int_to_nat in Hmn.
      by rewrite addnC in Hmn.
    rewrite (_ : qpoly_nonneg (q ^ (Negz n.+1 + 1) * (q ^ m * a)) n.+1 x 
               = qpoly_nonneg (q ^ (Negz n.+1 + 1) * (q ^ m * a))
                              (l.+1 + m) x).
      rewrite qpoly_nonneg_explaw.
      have -> : q ^ (Negz n.+1 + 1) * (q ^ m * a) =
                q ^ (Negz l.+1 + 1) * a.
        by rewrite mulrA -expfzDr // !NegzS addrC Hmn.
      have -> : q ^ l.+1 * (q ^ (Negz l.+1 + 1) * a) = a.
        by rewrite mulrA -expfzDr // NegzS NegzK expr0z mul1r.
      rewrite mulrA.
      rewrite [qpoly_nonneg (q ^ (Negz l.+1 + 1) * a) l.+1 x *
               qpoly_nonneg a m x] mulrC.
      rewrite red_frac_l //.
      have -> : a = q ^ l.+1 * (q ^ (Posz m + Negz n) * a) => //.
        by rewrite mulrA -expfzDr // Hmn NegzK expr0z mul1r.
      apply qpoly_exp_non0r.
      rewrite -Hmn' //.
    by rewrite Hmn'.
Qed.

Lemma qpoly_exp_neg_pos a m n x : q != 0 ->
  qpoly_nonneg (q ^ Negz m * a) m.+1 x != 0 ->
  qpoly a (Negz m + Posz n) x =
  qpoly a (Negz m) x * qpoly (q ^ Negz m * a) n x.
Proof.
  move=> Hq0 Hqpolym.
  case Hmn : (Negz m + n) => [l|l] /=.
  - rewrite /qpoly_neg.
    rewrite (_ : qpoly_nonneg (q ^ Negz m * a) n x =
                 qpoly_nonneg (q ^ Negz m * a)
                   (m.+1 + l) x).
      rewrite qpoly_nonneg_explaw.
      have -> : q ^ (Negz m.+1 + 1) * a = q ^ Negz m * a.
        by rewrite -addn1 Negz_addK.
      have -> : q ^ m.+1 * (q ^ Negz m * a) = a.
        by rewrite mulrA -expfzDr // NegzK expr0z mul1r.
      rewrite mulrC mulrA mulr1.
      rewrite -{2}[qpoly_nonneg (q ^ Negz m * a) m.+1 x]
                    mulr1.
      rewrite red_frac_l //.
      by rewrite divr1.
    move: Hmn.
    rewrite addrC.
    move /Negz_transp /eq_int_to_nat.
    by rewrite addnC => ->.
  - rewrite /qpoly_neg.
    have Hmn' : m.+1 = (n + l.+1)%N.
      rewrite addrC in Hmn.
      move /Negz_transp /esym in Hmn.
      rewrite addrC in Hmn.
      by move /Negz_transp /eq_int_to_nat in Hmn.
    rewrite {2}Hmn'.
    rewrite qpoly_nonneg_explaw.
    have -> : q ^ n * (q ^ (Negz m.+1 + 1) * a) =
                q ^ (Negz l.+1 + 1) * a.
      by rewrite mulrA -expfzDr // !NegzS addrC Hmn.
    have -> : q ^ (Negz m.+1 + 1) * a = q ^ Negz m * a.
      by rewrite NegzS.
    rewrite [RHS] mulrC mulrA red_frac_l //.

    apply (@qpoly_exp_non0l x _ n l.+1).
    by rewrite -Hmn'.
Qed.

Lemma qpoly_exp_neg_neg a m n x : q != 0 ->
  qpoly a (Negz m + Negz n) x =
  qpoly a (Negz m) x * qpoly (q ^ Negz m * a) (Negz n) x .
Proof.
  move=> Hq0 /=.
  rewrite /qpoly_neg.
  have -> : (m + n).+2 = ((n.+1) + (m.+1))%N.
    by rewrite addnC addnS -addn2.
  rewrite qpoly_nonneg_explaw.
  have -> : q ^ n.+1 * (q ^ (Negz (n.+1 + m.+1) + 1) * a) =
              q ^ (Negz m.+1 + 1) * a.
    rewrite mulrA -expfzDr //.
    have -> : Posz n.+1 + (Negz (n.+1 + m.+1) + 1) = Negz m.+1 + 1 => //.
    by rewrite Negz_add 2!addrA NegzK add0r.
  have -> : (q ^ (Negz n.+1 + 1) * (q ^ Negz m * a)) =
              (q ^ (Negz (n.+1 + m.+1) + 1) * a).
    by rewrite mulrA -expfzDr // NegzS -Negz_add addnS NegzS.
  rewrite mulf_div mulr1.
  by rewrite [qpoly_nonneg (q ^ (Negz (n.+1 + m.+1) + 1) * a) n.+1 x *
            qpoly_nonneg (q ^ (Negz m.+1 + 1) * a) m.+1 x] mulrC.
Qed.

Theorem qpoly_exp_law a m n x : q != 0 ->
  qpoly_denom a m x != 0 ->
  qpoly_denom (q ^ m * a) n x != 0 ->
  qpoly a (m + n) x = qpoly a m x * qpoly (q ^ m * a) n x.
Proof.
  move=> Hq0.
  case: m => m Hm.
  - case: n => n Hn.
    + by apply qpoly_nonneg_explaw.
    + rewrite qpoly_exp_pos_neg //.
      by rewrite addrC expfzDr // -mulrA.
  - case: n => n Hn.
    + rewrite qpoly_exp_neg_pos //.
    + by apply qpoly_exp_neg_neg.
Qed.

(* q-derivative of q-polynomial for 0 *)
Lemma qderiv_qpoly_0 a x :
  Dq (qpoly a 0) x = q_nat 0 * qpoly a (- 1) x.
Proof. by rewrite Dq_const q_nat_0 mul0r. Qed.

Lemma qpoly_qx a m n x : q != 0 ->
  qpoly_nonneg (q ^ m * a) n (q * x) =
    q ^ n * qpoly_nonneg (q ^ (m - 1) * a) n x.
Proof.
  move=> Hq0.
  elim: n => [|n IH] /=.
  - by rewrite expr0z mul1r.
  - rewrite IH.
    rewrite exprSzr -[RHS]mulrA.
    rewrite [q * (qpoly_nonneg (q ^ (m - 1) * a) n x *
              (x - q ^ n * (q ^ (m - 1) * a)))] mulrA.
    rewrite [q * qpoly_nonneg (q ^ (m - 1) * a) n x] mulrC.
    rewrite -[qpoly_nonneg (q ^ (m - 1) * a) n x * q *
               (x - q ^ n * (q ^ (m - 1) * a))] mulrA.
    rewrite [q * (x - q ^ n * (q ^ (m - 1) * a))] mulrBr.
    rewrite [q * (q ^ n * (q ^ (m - 1) * a))] mulrA.
    rewrite [q * q ^ n] mulrC.
    rewrite -[q ^ n * q * (q ^ (m - 1) * a)] mulrA.
    rewrite (_ : q * (q ^ (m - 1) * a) = q ^ m * a).
      by rewrite [RHS] mulrA.
    by rewrite mulrA -{1}(expr1z q) -expfzDr // addrC subrK.
Qed.

(* q-derivative of q-polynomial for neg *)
Theorem qderiv_qpoly_neg a n x : q != 0 -> x != 0 ->
  (x - q ^ (Negz n) * a) != 0 ->
  qpoly_nonneg (q ^ (Negz n + 1) * a) n x != 0 ->
  Dq (qpoly_neg a n) x = q_nat (Negz n + 1) * qpoly_neg a (n.+1) x.
Proof.
  move=> Hq0 Hx Hqn Hqpoly.
  destruct n.
  - by rewrite /Dq /dq /qpoly_neg /= addrK' q_nat_0 !mul0r.
  - rewrite qderiv_quot //.
      rewrite Dq_const mulr0 mul1r sub0r.
      rewrite qderiv_qpoly_nonneg // qpoly_qx // -mulNr.
      rewrite [qpoly_nonneg (q ^ (Negz n.+1 + 1) * a) n.+1 x *
                (q ^ n.+1 * qpoly_nonneg (q ^ (Negz n.+1 + 1 - 1) *
                  a) n.+1 x)] mulrC.
      rewrite -mulf_div.
      have -> : qpoly_nonneg (q ^ (Negz n.+1 + 1) * a) n x /
                    qpoly_nonneg (q ^ (Negz n.+1 + 1) * a) n.+1 x =
                      1 / (x - q ^ (- 1) * a).
        rewrite -(mulr1
                     (qpoly_nonneg (q ^ (Negz n.+1 + 1) * a) n x)) /=.
        rewrite red_frac_l.
          rewrite NegzE mulrA -expfzDr // addrA -addn2.
          rewrite (_ : Posz (n + 2)%N = Posz n + 2) //.
          rewrite -{1}(add0r (Posz n)).
          by rewrite addrKA.
        by rewrite /=; apply mulnon0 in Hqpoly.
      rewrite mulf_div.
      rewrite -[q ^ n.+1 *
                 qpoly_nonneg (q ^ (Negz n.+1 + 1 - 1) * a) n.+1 x *
                   (x - q ^ (-1) * a)]mulrA.
      have -> : qpoly_nonneg (q ^ (Negz n.+1 + 1 - 1) * a) n.+1 x *
                (x - q ^ (-1) * a) =
                qpoly_nonneg (q ^ (Negz (n.+1)) * a) n.+2 x => /=.
        have -> : Negz n.+1 + 1 - 1 = Negz n.+1.
          by rewrite addrK.
        have -> : q ^ n.+1 * (q ^ Negz n.+1 * a) = q ^ (-1) * a => //.
        rewrite mulrA -expfzDr // NegzE.
        have -> : Posz n.+1 - Posz n.+2 = - 1 => //.
        rewrite -addn1 -[(n + 1).+1]addn1.
        rewrite (_ : Posz (n + 1)%N = Posz n + 1) //.
        rewrite (_ : Posz (n + 1 + 1)%N = Posz n + 1 + 1) //.
        rewrite -(add0r (Posz n + 1)).
        by rewrite addrKA.
      rewrite /qpoly_neg /=.
      rewrite (_ : Negz n.+2 + 1 = Negz n.+1) //.
      rewrite -mulf_div.
      congr (_ * _).
      rewrite NegzE mulrC.
      rewrite /q_nat.
      rewrite -mulNr mulrA.
      congr (_ / _).
      rewrite opprB mulrBr mulr1 mulrC divff.
        rewrite invr_expz.
        rewrite (_ : - Posz n.+2 + 1 = - Posz n.+1) //.
        rewrite -addn1.
        rewrite (_ : Posz (n.+1 + 1)%N = Posz n.+1 + 1) //.
        rewrite addrC.
        rewrite [Posz n.+1 + 1]addrC.
        by rewrite -{1}(add0r 1) addrKA sub0r.
      by rewrite expnon0 //.
    rewrite qpoly_qx // mulf_neq0 //.
      by rewrite expnon0.
    rewrite qpoly_nonneg_head mulf_neq0 //.
    rewrite (_ : Negz n.+1 + 1 - 1 = Negz n.+1) //.
      by rewrite addrK.
    move: Hqpoly => /=.
    move/mulnon0.
    by rewrite addrK mulrA -{2}(expr1z q) -expfzDr.
Qed.

Theorem qderiv_qpoly a n x : q != 0 -> x != 0 ->
  x - q ^ (n - 1) * a != 0 ->
  qpoly (q ^ n * a) (- n) x != 0 ->
  Dq (qpoly a n) x = q_nat n * qpoly a (n - 1) x.
Proof.
  move=> Hq0 Hx Hxqa Hqpoly.
  case: n Hxqa Hqpoly => [|/=] n Hxqa Hqpoly.
  - destruct n.
    + by rewrite qderiv_qpoly_0.
    + rewrite qderiv_qpoly_nonneg //.
      rewrite (_ : Posz n.+1 - 1 = n) //.
      rewrite -addn1.
      rewrite (_ : Posz (n + 1)%N = Posz n + 1) //.
      by rewrite addrK.
  - rewrite Dq_qpoly_int_to_neg qderiv_qpoly_neg //.
        rewrite Negz_addK.
        rewrite (_ : (n + 1).+1 = (n + 0).+2) //.
        by rewrite addn0 addn1.
      rewrite (_ : Negz (n + 1) = Negz n - 1) //.
      by apply itransposition; rewrite Negz_addK.
    by rewrite Negz_addK addn1.
Qed.

Fixpoint q_fact n := match n with
  | 0 => 1
  | n.+1 => q_fact n * q_nat n.+1
  end.

Lemma q_fact_nat_non0 n : q_fact n.+1 != 0 -> q_nat n.+1 != 0.
Proof.
  rewrite /= mulrC.
  by apply mulnon0.
Qed.

(* Lemma q_fact_non0 n : q_fact n != 0.
Proof.
  elim: n => [|n IH] //=.
  - by apply oner_neq0.
  - Search (_ * _ != 0).
    apply mulf_neq0 => //.
Admitted. *)

Definition q_bicoef n j :=
  q_fact n / (q_fact j * q_fact (n - j)).

(* Lemma q_fact1 n : (n <= 0)%N -> q_fact n = 1.
Proof.
  move=> Hn.
  have -> : (n = 0)%N => //.
  apply /eqP.
  by rewrite -(subn0 n) subn_eq0 //. 
Qed. *)

(*Lemma q_bicoef_jn n j : (n - j <= 0)%N ->
  q_coef n j = q_fact n / q_fact j.
Proof.
  move=> Hjn.
  rewrite /q_coef.
  by rewrite (q_fact1 (n - j)%N) // mulr1.
Qed. *)

(* Lemma q_fact_jn n j : (n - j <= 0)%N ->
  q_fact j = q_fact (n - (n - j)).
Proof.
Qed. *)

Lemma q_bicoefE n j : (j <= n)%N ->
  q_bicoef n (n - j) = q_bicoef n j.
Proof.
  move=> Hjn.
  rewrite /q_bicoef.
  rewrite subKn //.
  by rewrite [q_fact (n - j) * q_fact j] mulrC.
Qed.

Lemma q_pascal n j : (j < n)%N ->
  q_fact j.+1 != 0 ->
  q_fact (n - j) != 0 ->
  q_bicoef n.+1 j.+1 = q_bicoef n j +
                 q ^ j.+1 * q_bicoef n j.+1.
Proof.
  move=> Hjn Hj0 Hnj0.
  rewrite [LHS] /q_bicoef.
  rewrite [q_fact n.+1] /=.
  rewrite (q_nat_cat j) // mulrDr.
  rewrite -add_div.
    have -> : q_fact n * q_nat j.+1 / (q_fact j.+1 * q_fact (n.+1 - j.+1)) =
              q_bicoef n j.
      rewrite -mulrA -(mul1r (q_nat j.+1)).
      rewrite [q_fact j.+1 * q_fact (n.+1 - j.+1)] mulrC /=.
      rewrite [q_fact (n.+1 - j.+1) * (q_fact j * q_nat j.+1)] mulrA.
      rewrite red_frac_r //.
        rewrite mul1r subSS.
        by rewrite [q_fact (n - j) * q_fact j] mulrC.
      by apply q_fact_nat_non0.
    rewrite mulrA.
    rewrite [q_fact n * q ^ j.+1] mulrC subSS.
    rewrite -subnSK //.
    rewrite [q_fact (n - j.+1).+1] /=.
    rewrite mulrA red_frac_r.
      by rewrite mulrA.
    apply q_fact_nat_non0.
    rewrite subnSK //.
  by apply mulf_neq0.
Qed.

End q_analogue.

Section q_chain_rule.
Local Open Scope ring_scope.
Variable (R : realType).

Lemma qchain q u f a b x : dq R q u x != 0 -> u = (fun x => a * x ^ b) ->
  Dq R q (f \o u) x = (Dq R (q^b) f (u x)) * (Dq R q u x).
Proof.
  move=> Hqu Hu.
  rewrite Hu /Dq /dq mulf_div /=.
  rewrite [(q ^ b * (a * x ^ b) - a * x ^ b) * (q * x - x)] mulrC.
  rewrite expfzMl !mulrA.
  rewrite [a * q ^ b] mulrC.
  rewrite red_frac_r //.
  move: Hqu.
  by rewrite /dq Hu expfzMl mulrA mulrC.
Qed.
End q_chain_rule.