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
From mathcomp Require Import all_algebra.
Require Import q_tools.

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
Check Dq.

Fixpoint hoDq n f := match n with
  | 0 => f
  | n.+1 => Dq (hoDq n f)
  end.

(* q-derivative for const is 0 *)
Lemma Dq_const x c : Dq (fun x => c) x = 0.
Proof. by rewrite /Dq /dq addrK' mul0r. Qed.

(* q-derivative is linear *)
Lemma Dq_is_linear a b f g x :
  Dq ((a */ f) \+ (b */ g)) x = a * (Dq f x) + b * (Dq g x).
Proof.
  rewrite /Dq /dq !mulrA.
  case Hx : (x == 0).
  - move: Hx => /eqP ->.
    by rewrite mulr0 !addrK' !mulr0 -mulrDl addr0.
  - rewrite add_div.
      rewrite !mulrBr opprD !addrA.
      rewrite [a * f (q * x) + b * g (q * x) - a * f x]
              addrC.
      rewrite [(a * f (q * x) + b * g (q * x))]
              addrC.
      rewrite addrA.
      rewrite [- (a * f x) + b * g (q * x) + a * f (q * x)]
              addrC.
      by rewrite addrA.
  apply denom_is_nonzero => //.
  by rewrite Hx.
Qed.

(* q-analogue of natural number *)
Definition q_nat n : R := (q ^ n - 1) / (q - 1).

Definition Dq' (p : {poly R}) := \poly_(i < size p) (q_nat (i.+1) * p`_i.+1).

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
      apply (same_prod _ (q - 1)) => //.
      by rewrite mulrDl !denomK // mulrBr mulr1 -exprSzr
                [RHS] addrC subrKA.
    rewrite IH.
    rewrite [RHS] (@big_cat_nat _ _ _ n.+1) //=.
    by rewrite big_nat1.
Qed.

Lemma q_nat_cat {n} j : (j < n)%N ->
  q_nat n.+1 = q_nat j.+1 + q ^ j.+1 * q_nat (n.+1 - j.+1)%N.
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
  have {2}-> : j.+1 = (0 + j.+1)%N by [].
  rewrite big_addn.
  have -> : (n.+1 - j.+1)%N = (n.+1 - j.+1 - 1).+1.
    by rewrite subn1 prednK // // subn_gt0.
  congr (_ + _).
  under eq_bigr do rewrite exprzD_nat.
  by rewrite sum_distr q_natE.
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

(* Lemma lim_q_nat n : forall e : R, e > 0 ->
  exists d, `|q - 1| < d -> `|n%:R - (q_nat n)| < e.
Proof.
  move=> e He.
  destruct n.
  - eexists => _.
    by rewrite q_nat_0 addrK' Num.Theory.normr0.
  - exists (e / n%:R).
Admitted. *)

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
  by rewrite (mulfC _ f g) qderiv_prod // addrC.
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
    apply /rtransposition /(same_prod _ (g (q * x))) => //.
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
    apply /rtransposition /(same_prod _ (g x)) => //.
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

Fixpoint qpoly_nonneg_poly a n :=
  match n with
  | 0 => 1
  | n.+1 => (qpoly_nonneg_poly a n) * ('X - (q ^ n * a)%:P)
  end.

Lemma qpoly_size a n : size (qpoly_nonneg_poly a n) = n.+1.
Proof.
  elim: n => [|n IH] => //=.
  - by rewrite size_poly1.
  - rewrite size_Mmonic.
        by rewrite IH size_XsubC addn2.
      by rewrite -size_poly_gt0 IH.
    by apply monicXsubC.
Qed.

Lemma qpoly_nonnegE a n x :
  qpoly_nonneg a n x = (qpoly_nonneg_poly a n).[x].
Proof.
  elim: n => [|n IH] //=.
  - by rewrite hornerC.
  - by rewrite hornerM -IH hornerXsubC.
Qed.

Lemma qpoly_nonneg_head a n x:
   qpoly_nonneg a n.+1 x =
  (x - a) * qpoly_nonneg (q * a) n x.
Proof.
  elim: n => [|n IH] /=.
  - by rewrite expr0z !mul1r mulr1.
  - by rewrite !mulrA -IH exprSzr.
Qed.

Lemma qpolyxa a n : qpoly_nonneg a n.+1 a = 0.
Proof. by rewrite qpoly_nonneg_head addrK' mul0r. Qed.

Lemma qpolyx0 a n :
  qpoly_nonneg (- a) n 0 = q ^ Posz ((n * (n - 1)) ./2) * a ^ n.
Proof.
  elim: n => [| n IH] //.
  - by rewrite mul0n /= expr0z expr0z mulr1.
  - destruct n.
      by rewrite /= !mul1r sub0r opp_oppE expr1z.
    case Hq0 : (q == 0).
    + rewrite qpoly_nonneg_head.
      destruct n.
        rewrite /= expr0z.
        move: Hq0 => /eqP ->.
        by rewrite opp_oppE add0r mul1r expr1z sub0r !mul0r mul1r oppr0 mulr0.
      rewrite qpoly_nonneg_head.
      move: Hq0 => /eqP ->.
      rewrite mul0r subr0 mulrA !mulr0 !mul0r.
      have -> : (n.+3 * (n.+3 - 1))./2 =
                ((n.+3 * (n.+3 - 1))./2 - 1)%N.+1.
        by rewrite -[RHS]addn1 subnK.
      by rewrite exp0rz' mul0r.
    + rewrite /= in IH.
      rewrite [LHS] /= IH // sub0r -mulrN opp_oppE.
      rewrite [q ^ n.+1 * a] mulrC.
      rewrite mulrA mulrC 2!mulrA -expfzDr.
        have -> : Posz n.+1 + (n.+1 * (n.+1 - 1))./2 =
                  (n.+2 * (n.+2 - 1))./2.
        by rewrite !subn1 /= half_add.
    by rewrite -mulrA -(exprSzr a n.+1).
  by move: Hq0 ->.
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
    apply (eq_int_to_nat R) in Hmn.
    by rewrite Hmn.
  - rewrite /qpoly_neg.
    have Hmn' : n.+1 = (l.+1 + m)%N.
      move /Negz_transp /esym in Hmn.
      rewrite addrC in Hmn.
      move /Negz_transp /(eq_int_to_nat R) in Hmn.
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
      by move /Negz_transp /(eq_int_to_nat R) in Hmn.
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

Lemma q_fact_lenon0 m n : q_fact (m + n) != 0 -> q_fact m != 0.
Proof.
  elim: n => [|n IH].
  - by rewrite addn0.
  - rewrite addnS /=.
    move/ mulnon0.
    apply IH.
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

Lemma q_bicoefnn n : q_fact n != 0 -> q_bicoef n n = 1.
Proof.
  move=> H.
  rewrite /q_bicoef.
  by rewrite -{3}(addn0 n) addKn /= mulr1 divff.
Qed.

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

Fixpoint hoD {A} D n (f : A) := match n with
  | 0 => f
  | n.+1 => D (hoD D n f)
  end.

Notation "D \^ n" := (hoD D n) (at level 49).

Definition islinear (D : {poly R} -> {poly R}) :=
  forall a b f g, D ((a *: f) + (b *: g)) = a *: D f + b *: D g.

Lemma linear_add D f g : islinear D -> D (f + g) = D f + D g.
Proof.
  move=> HlD.
  by rewrite -(scale1r f) -(scale1r g) HlD !scale1r.
Qed.

Lemma linear0 D : islinear D -> D 0 = 0.
Proof.
  move=> HlD.
  by rewrite -(addr0 0) -(scale0r 0%:P) HlD !scale0r.
Qed.

Lemma nth_islinear D n : islinear D -> islinear (D \^ n).
Proof.
  elim: n => [|n IH] //=.
  move=> HlD a b f g.
  by rewrite IH.
Qed.

Lemma linear_distr D n c F : islinear D ->
  D (\sum_(0 <= i < n.+1) c i *: F i) = \sum_(0 <= i < n.+1) c i *: D (F i).
Proof.
  move=> HlD.
  elim: n => [|n IH].
  - rewrite !big_nat1.
    have -> : c 0%N *: F 0%N = c 0%N *: F 0%N + 0 *: 0%:P.
      by rewrite scale0r addr0.
    by rewrite HlD scale0r addr0.
  - rewrite (@big_cat_nat _ _ _ n.+1) //=.
    rewrite big_nat1.
    rewrite -(scale1r (\sum_(0 <= i < n.+1) c i *: F i)).
    rewrite HlD scale1r IH.
    rewrite [RHS] (@big_cat_nat _ _ _ n.+1) //=.
    by rewrite big_nat1.
Qed.

Lemma linear_distr' D j n c F : islinear D -> (j < n)%N ->
  D (\sum_(j.+1 <= i < n.+1) c i *: F i) =
  \sum_(j.+1 <= i < n.+1) c i *: D (F i).
Proof.
  move=> HlD Hjn.
  have Hjn' : (j < n.+1)%N.
    by apply ltnW.
  move: (linear_distr D n c F HlD).
  rewrite (@big_cat_nat _ _ _ j.+1) //=.
  rewrite linear_add // linear_distr //.
  rewrite (@big_cat_nat _ _ _ j.+1 0 n.+1) //=.
  by move /same_addl.
Qed.

Definition isfderiv D (P : nat -> {poly R}) := forall n,
 match n with
  | 0 => (D (P n)) = 0
  | n.+1 => (D (P n.+1)) = P n
  end.

(* Lemma poly_basis' n (P : nat -> {poly R}) (f : {poly R}) :
  (forall m, (m <= n)%N -> size (P m) = m.+1) ->
  (size f <= n.+1)%N ->
  exists (c : nat -> R), f = \sum_(0 <= i < n.+1)
          (c i *: (P i)).
Proof.
Admitted. *)

Lemma poly_basis n (P : nat -> {poly R}) (f : {poly R}) :
  (forall m, size (P m) = m.+1) ->
  (size f <= n.+1)%N ->
  exists (c : nat -> R), f = \sum_(0 <= i < n.+1)
          (c i *: (P i)).
Proof.
  elim: n.+1 f => {n} [|n IH] f HP Hf //=.
  - exists (fun i => 0).
    rewrite big_nil.
    move: Hf.
    by rewrite leqn0 -/(nilp f) nil_poly => /eqP.
  - set cn := f`_n / (P n)`_n.
    set f' := f - cn *: P n.
    destruct (IH f') as [c Hc] => //.
      have Hf' : (size f' <= n.+1)%N.
        rewrite /f' -scaleNr.
        move: (size_add f (- cn *: P n)).
        rewrite leq_max.
        move /orP => [H1 | H2].
        + by apply (leq_trans H1 Hf).
        + move: (size_scale_leq (- cn) (P n)).
          move: (HP n) -> => HP'.
          by apply (leq_trans H2 HP').
      have Hf'n : f'`_n = 0.
        rewrite /f' /cn coefB coefZ denomK ?addrK' //.
        have {2}-> : n = n.+1.-1 by [].
        move: (HP n) <-.
        rewrite -lead_coefE.
        case H : (lead_coef (P n) == 0) => //.
        move: H.
        rewrite lead_coef_eq0 -size_poly_eq0.
        by move: (HP n) ->.
      move /leq_sizeP in Hf'.
      have Hf'' : forall j : nat, (n <= j)%N -> f'`_j = 0.
        move=> j.
        rewrite leq_eqVlt.
        move/orP => [/eqP <-|] //.
        by apply Hf'.
      by apply /leq_sizeP.
    exists (fun i => if i == n then cn else c i).
    rewrite big_nat_recr //=.
    under eq_big_nat => i /andP [_].
      rewrite ltn_neqAle => /andP [/negbTE ] -> _.
    over.
    by rewrite -Hc eqxx /f' subrK.
Qed.

Lemma hornersumD m n P (a : R) :
  (\sum_(m <= j < n.+1) P j).[a] = (\sum_(m <= j < n.+1) (P j).[a]).
Proof.
  have -> : (m = 0 + m)%N by [].
  rewrite !big_addn.
  elim: (n.+1 - m)%N => {n} [|n IH] //=.
  - by rewrite !big_nil horner0.
  - rewrite (@big_cat_nat _ _ _ n) //= big_nat1.
    rewrite hornerD IH.
    by rewrite [RHS] (@big_cat_nat _ _ _ n) //= big_nat1.
Qed.

Lemma nthisfderiv_pos j D P : isfderiv D P ->
  forall i, (i >= j)%N -> (D \^ j) (P i) = P (i - j)%N.
Proof.
  move=> Hd i.
  elim: j => [|j IH] Hij //=.
  - by rewrite subn0.
  - rewrite IH.
      have -> : (i - j)%N = (i - j.+1)%N.+1.
        rewrite -subSn // subSS.
      by apply (Hd _.+1).
    by apply ltnW.
Qed.

Lemma nthisfderiv_0 j D P : islinear D -> isfderiv D P ->
  forall i, (i < j)%N -> (D \^ j) (P i) = 0.
Proof.
  move=> HlD Hd i.
  elim: j => [|j IH] Hij //=.
  case Hij' : (i == j).
  - move: (Hij') => /eqP ->.
    rewrite nthisfderiv_pos // subnn.
    by apply (Hd 0%N).
  - have Hij'' : (i < j)%N.
      rewrite ltn_neqAle.
      apply /andP; split.
      + by rewrite Hij'.
      + by rewrite -ltnS.
    by rewrite IH // linear0.
Qed.

Theorem general_Taylor D n P (f : {poly R}) a :
  islinear D -> isfderiv D P ->
  (P 0%N).[a] = 1 ->
  (forall n, (P n.+1).[a] = 0) ->
  (forall m, size (P m) = m.+1) ->
  size f = n.+1 ->
  f = \sum_(0 <= i < n.+1)
          (((D \^ i) f).[a] *: (P i)).
Proof.
  move=> Hl Hd HP0 HP HdP Hdf.
  have Hdf' : (size f <= n.+1)%N.
    by rewrite Hdf leqnn.
  move: (poly_basis n P f HdP Hdf') => [c] Hf.
  have Hc0 : c 0%N = ((D \^ 0) f).[a] => /=.
    rewrite Hf.
    destruct n.
      by rewrite big_nat1 hornerZ HP0 mulr1.
    rewrite hornersumD.
    rewrite (@big_cat_nat _ _ _ 1) //= big_nat1.
    rewrite hornerZ HP0 mulr1.
    have -> : (1 = 0 + 1)%N by [].
    rewrite big_addn subn1 /=.
    under eq_big_nat => i /andP [_ _].
      rewrite hornerZ addn1 HP mulr0.
    over.
    by rewrite big1 // addr0.
  have ithD : forall j, (j.+1 <= n)%N ->
    (D \^ j.+1) f = \sum_(j.+1 <= i < n.+1) c i *: P (i - j.+1)%N.
    move=> j Hj.
    rewrite Hf linear_distr.
      rewrite {1}(lock j.+1).
      rewrite (@big_cat_nat _ _ _ j.+1) //=.
        rewrite -lock.
        under eq_big_nat => i /andP [_ Hi].
          rewrite nthisfderiv_0 // scaler0.
        over.
        rewrite big1 // add0r.
        by under eq_big_nat => i /andP [Hi _] do rewrite nthisfderiv_pos //.
      by apply leqW.
    by apply nth_islinear.
  have coef : forall j, (j <= n)%N -> c j = ((D \^ j) f).[a].
    move=> j Hj.
    destruct j => //.
    rewrite ithD //.
    rewrite (@big_cat_nat _ _ _ j.+2) //= big_nat1 hornerD.
    rewrite subnn hornerZ HP0 mulr1 hornersumD.
    under eq_big_nat => i /andP [Hi Hi'].
      rewrite hornerZ.
      move: (Hi).
      rewrite -addn1 -leq_subRL //; last by apply ltnW.
      case: (i - j.+1)%N => // k Hk.
      rewrite HP mulr0.
    over.
    move=> /=.
    by rewrite big1 // addr0.
  rewrite {1}Hf.
  rewrite big_nat_cond.
  rewrite [RHS] big_nat_cond.
  apply eq_bigr => i /andP [/andP [Hi Hi'] _].
  by rewrite coef.
Qed.

(* Lemma Dq_isfderiv n a x : x != 0 -> q_fact n != 0 ->
  isfderiv Dq n (fun i : nat => qpoly_nonneg_poly a i / (q_fact i)%:P) x.
Proof.
  move=> Hx Hfact.
  rewrite /isfderiv.
  rewrite /deriv_to_poly.
  destruct n => //=.
  - by rewrite polyCV invr1 mulr1 /Dq /dq !hornerC addrK' mul0r.
  - rewrite !polyCV /Dq /dq !hornerM !hornerXsubC !hornerC.
    rewrite -!qpoly_nonnegE.
    have -> : (qpoly_nonneg a n (q * x) * (q * x - q ^ n * a) /
              (q_fact n * q_nat n.+1) -
              qpoly_nonneg a n x * (x - q ^ n * a) /
              (q_fact n * q_nat n.+1)) / (q * x - x) =
              Dq (qpoly_nonneg a n.+1) x / q_fact n.+1.
      by rewrite /Dq /dq /= -mulrBl denom_comm.
    rewrite qderiv_qpoly_nonneg //=.
    rewrite [q_fact n * q_nat n.+1] mulrC red_frac_l //.
    by apply q_fact_nat_non0.
Qed. *)

Definition polyderiv (D : (R -> R) -> (R -> R)) (p : {poly R}) :=
  D (fun (x : R) => p.[x]).

Notation "D # p" := (polyderiv D p) (at level 49).

Lemma poly_happly p p' (x : R) : p = p' -> p.[x] = p'.[x].
Proof. by move=> ->. Qed.

(* Lemma poly_funext p p' : (forall (x : R),  p.[x] = p'.[x]) -> p = p'.
Proof.
Admitted. *)

Lemma sumW n (a F : nat -> R) :
  \sum_(i < n) (a i * F i) = \sum_(0 <= i < n) (a i * F i).
Proof. by rewrite big_mkord. Qed.

Lemma Dq'E p x : x != 0 -> (Dq' p).[x] = (Dq # p) x.
Proof.
  move=> Hx.
  rewrite /Dq' /(_ # _) /Dq /dq.
  rewrite horner_poly !horner_coef.
  rewrite (sumW _ (fun i => (q_nat i.+1 * p`_i.+1))) !sumW sum_sub.
  case Hsize : (size p == 0%N).
  - rewrite size_poly_eq0 in Hsize.
    move/eqP : (Hsize) ->.
    by rewrite size_poly0 !big_nil mul0r.
  - have Hsize' : (0 < size p)%N.
      rewrite ltn_neqAle.
      apply /andP; split => //.
      move: Hsize.
      by rewrite eq_sym => ->.
    rewrite mulrC -sum_distr.
    rewrite [RHS](@big_cat_nat _ _ _ 1 0 (size p)) //=.
    rewrite !big_nat1 !expr0 addrK' mul0r add0r.
    have -> : (1 = 0 + 1)%N by [].
    rewrite big_addn.
    rewrite (@big_cat_nat _ _ _ (size p - 1)) //=.
      have -> : \sum_(size p - 1 <= i < size p)
                  q_nat i.+1 * p`_i.+1 * x ^+ i = 0.
        under eq_big_nat => i /andP [Hi Hi'].
          move : Hi.
          rewrite leq_subLR addnC addn1.
          move/leq_sizeP -> => //.
          rewrite mulr0 mul0r.
        over.
        by rewrite big1.
      rewrite addr0.
      apply eq_big_nat => i /andP [Hi Hi'].
      rewrite addn1 /q_nat.
      have -> : (q * x) ^+ i.+1 = (q * x) ^ (Posz i.+1) by [].
      have -> : x ^+ i.+1 = 1 * x ^+ i.+1.
        by rewrite mul1r.
      have {5}-> : x = 1 * x.
        by rewrite mul1r.
      rewrite expfzMl -mulrBr -!mulrBl -mulf_div -!mulrA.
      rewrite [p`_i.+1 * x ^+ i]mulrC [RHS]mulrC !mulrA.
      congr (_ * _).
      rewrite [(q - 1)^-1 * (q ^ i.+1 - 1)]mulrC -!mulrA.
      congr (_ * _).
      congr (_ * _).
      by rewrite exprSzr -mulrA divff // mulr1.
    by rewrite leq_subLR.
Qed.

(* Lemma Dq_poly_q0 p x : x != 0 -> q = 0 ->
  (Dq # p) x = (\poly_(i < (size p)) p`_i.+1).[x].
Proof.
Qed. *)

Lemma hoDq'_q0 n p : q = 0 ->
  (Dq' \^ n) p = \poly_(i < size p) p`_(i + n).
Proof.
  move=> Hq0.
  elim: n => [|n IH] //=.
  - apply polyP => j.
    rewrite coef_poly.
    case Hj : (j < size p)%N.
    + by rewrite addn0.
    + have Hj' : (size p <= j)%N by rewrite leqNgt Hj.
      by move/leq_sizeP : Hj' ->.
  - rewrite IH {1}/Dq'.
    rewrite (polyW _ _ (size p)).
      have -> : \poly_(i < size p) p`_(i + n.+1) =
                \sum_(0 <= i < size p) p`_(i + n.+1) *: 'X^i. admit.
      under eq_big_nat => j Hj.
        rewrite q_nat0.
Admitted.

Lemma hoDq'_q0E (p : {poly R}) x n: q = 0 -> x != 0 ->
  ((Dq' \^ n) p).[x] = ((Dq \^ n) # p) x.
Proof.
  move=> Hq0 Hx.
  rewrite hoDq'_q0 // /(_ # _).
  elim: n => [|n IH] //=.
  - admit.
  - rewrite {1}/Dq /dq -IH //=.
    rewrite Hq0 mul0r.
Admitted.

(* q != 0 ? *)
Lemma hoDq'E p x n : x != 0 -> ((Dq' \^ n) p).[x] = ((Dq \^ n) # p) x.
Proof.
  move=> Hx.
  case Hq0 : (q == 0).
  - rewrite hoDq'_q0E //.
    by apply /eqP.
  - rewrite /(_ # _).
    elim: n x Hx => [|n IH] x Hx //=.
    rewrite Dq'E // {2}/Dq /dq -!IH //.
    apply mulf_neq0 => //.
    by rewrite Hq0.
Qed.

Lemma Dq'_islinear_add (p p' : {poly R}) : Dq' (p + p') = Dq' p + Dq' p'.
Proof.
  rewrite /Dq'.
  rewrite (polyW R (p + p') (maxn (size p) (size p'))).
    rewrite (polyW R p (maxn (size p) (size p'))).
      rewrite (polyW R p' (maxn (size p) (size p'))).
        rewrite sum_add.
        by under eq_bigr do rewrite coefD mulrDr scalerDl.
      by apply leq_maxr.
    by apply leq_maxl.
  by apply size_add.
Qed.

Lemma Dq'_islinear_scale a p : Dq' (a *: p) = a *: Dq' p.
Proof.
  rewrite /Dq'; apply polyP => j.
  case Ha : (a == 0).
  - move/eqP : Ha ->; rewrite !scale0r.
    by rewrite coef_poly size_poly0 //= coef0.
  - have Ha' : a != 0 by rewrite Ha.
    rewrite size_scale // coefZ !coef_poly.
    case : (j < size p)%N.
    + by rewrite -scalerAr coefZ.
    + by rewrite mulr0.
Qed.

Lemma Dq'_islinear : islinear Dq'.
Proof.
  move=> a b p p'.
  by rewrite Dq'_islinear_add !Dq'_islinear_scale.
Qed.

Lemma Dq'_isderiv a : (forall n, q_fact n != 0) ->
  isfderiv Dq' (fun i : nat => qpoly_nonneg_poly a i / (q_fact i)%:P).
Proof.
Admitted.

Lemma q_Taylor_a0 n (f : {poly R}) x :
  (forall n, q_fact n != 0) ->
  size f = n.+1 ->
  f.[x] =  \sum_(0 <= i < n.+1)
             ((Dq \^ i) # f) 0 * qpoly_nonneg 0 i x / q_fact i.
Proof.
Admitted.

Theorem q_Taylor n (f : {poly R}) x a :
  (forall n, q_fact n != 0) ->
  size f = n.+1 ->
  f.[x] =  \sum_(0 <= i < n.+1)
             ((Dq \^ i) # f) a * qpoly_nonneg a i x / q_fact i.
Proof.
  move=> Hfact Hsf.
  case Ha : (a == 0).
    move/eqP : Ha ->.
    by rewrite (q_Taylor_a0 n).
  have Ha' : a != 0 by rewrite Ha.
  under eq_bigr do rewrite qpoly_nonnegE.
  rewrite sum_poly_div.
  under eq_bigr do rewrite -hornerZ.
  rewrite -hornersumD.
  apply poly_happly.
  under eq_bigr do rewrite -hoDq'E //.
  apply general_Taylor => //.
  - apply Dq'_islinear.
  - by apply Dq'_isderiv.
  - by rewrite invr1 mulr1 hornerC.
  - move=> m.
    by rewrite hornerM -qpoly_nonnegE qpolyxa mul0r.
  - move=> m.
    rewrite polyCV mulrC size_Cmul.
      by rewrite qpoly_size.
    by apply /invr_neq0.

(*     move: Hfact.
    have -> : n = (m + (n - m))%N.
      rewrite subnKC.
    by apply /q_fact_lenon0. *)
(*   - move=> a' b f' g.
    apply funext => x'.
    by apply Dq_is_linear.
  - by apply Dq_isfderiv.
  - by rewrite invr1 mulr1 hornerC.
  - move=> m.
    by rewrite hornerM -qpoly_nonnegE qpolyxa mul0r.
  - move=> m Hm.
    rewrite polyCV mulrC size_Cmul.
      by rewrite qpoly_size.
    apply /invr_neq0.
    move: Hfact.
    have -> : n = (m + (n - m))%N.
      by rewrite subnKC.
    by apply /q_fact_lenon0. *)
Qed.

Lemma Gauss_binomial x a n : q_fact n != 0 ->
  qpoly (-a) (Posz n) x =
  \sum_(0 <= i < n.+1)
    ((q_bicoef n i) * q ^ (Posz i * (Posz i - 1) / 2)
                    * (-a)^ i * x ^ (Posz n - Posz i)).
Proof.

  elim: n => [_ |/= n IH Hfact] //=.
  - by rewrite big_nat1 /q_bicoef !mulr1 !mul1r invr1.
  - rewrite (@big_cat_nat R _ _ n.+1 0 n.+2) //=.
    rewrite big_nat1 //=.
    rewrite IH.
      rewrite q_bicoefnn // addrN expr0z mulr1 mul1r.
Admitted.

(* f is a function ver *)
(* Theorem general_Taylor D n (P : nat -> {poly R}) f x a :
  isleniar D -> isfderiv D n P ->
  (P 0%N).[a] = 1 ->
  (forall n, (P n.+1).[a] = 0) ->
  (forall n, size (P n) = n) ->
  f x = \sum_(0 <= i < n.+1)
          ((hoD D n f) a * (P i).[x]).
Proof.
Admitted. *)

(* Theorem q_Taylor' f x n c {e} :
  (forall x, f x = \sum_(0 <= i < n.+1) e i * x^i) ->
  f x =  \sum_(0 <= i < n.+1)
             ((hoDq i f) c * qpoly c (Posz i ) x / q_fact i).
Proof.

(*   elim: n => [|n IH] Hf //=.
  - rewrite !big_nat1 //=.
    have Hf' : forall x, f x = e 0%N.
      move=> x'.
      by rewrite Hf big_nat1 expr0z mulr1.
    by rewrite (Hf' x) (Hf' c) mulr1 divr1.
  - rewrite (@big_cat_nat R _ _ n.+1 0 n.+2) //=.
    rewrite IH.
    rewrite big_nat1.
    have H : forall n, *)
Admitted. *)

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