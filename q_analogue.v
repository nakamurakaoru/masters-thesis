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
  rewrite [g x * f (q * x)] mulrC.
  by rewrite [g x * f x] mulrC subrKA.
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
      rewrite [a * f (q * x) + b * g (q * x) - a * f x]addrC.
      rewrite [(a * f (q * x) + b * g (q * x))]addrC addrA.
      rewrite [- (a * f x) + b * g (q * x) + a * f (q * x)] addrC.
      by rewrite addrA.
  apply denom_is_nonzero => //.
  by rewrite Hx.
Qed.

(* q-analogue of natural number *)
Definition q_nat n : R := (q ^ n - 1) / (q - 1).

(* q_nat 0 is 0 *)
Lemma q_nat0 : q_nat 0 = 0.
Proof. by rewrite /q_nat expr0z addrK' mul0r. Qed.

Lemma q_nat1 : q_nat 1 = 1.
Proof. by rewrite /q_nat expr1z divff. Qed.

Lemma q_natE (n : nat) : q_nat n.+1 = \sum_(0 <= i < n.+1) (q ^ i).
Proof.
  elim: n => [|n IH].
  - by rewrite q_nat1 big_nat1 expr0z.
  - have -> : q_nat n.+2 = q_nat n.+1 + q ^ n.+1.
      apply (same_prod _ (q - 1)) => //.
      by rewrite mulrDl !denomK // mulrBr mulr1 -exprSzr [RHS]addrC subrKA.
    by rewrite IH [RHS](@big_cat_nat _ _ _ n.+1) //= big_nat1.
Qed.

Lemma q_nat_cat {n} j : (j < n)%N ->
  q_nat n.+1 = q_nat j.+1 + q ^ j.+1 * q_nat (n.+1 - j.+1)%N.
Proof.
  move=> Hjn.
  have Hjn' : (j < n.+1)%N by apply ltnW.
  have Hjn'' : (0 < n.+1 - j.+1)%N.
    by rewrite subn_gt0.
  rewrite !q_natE (@big_cat_nat _ _ _ j.+1) //=.
  have {2}-> : j.+1 = (0 + j.+1)%N by [].
  rewrite big_addn.
  have -> : (n.+1 - j.+1)%N = (n.+1 - j.+1 - 1).+1.
    by rewrite subn1 prednK // // subn_gt0.
  f_equal.
  under eq_bigr do rewrite exprzD_nat.
  by rewrite sum_distr q_natE.
Qed.

Lemma q_nat_cat1 n : q_nat n.+1 = 1 + q * q_nat n.
Proof.
destruct n.
- by rewrite q_nat1 q_nat0 mulr0 addr0.
- by rewrite (q_nat_cat 0) ?q_nat1 ?expr1z ?subn1.
Qed.

Lemma q_nat_catn n : q_nat n.+1 = q_nat n + q ^ n.
Proof.
destruct n.
- by rewrite q_nat1 q_nat0 add0r expr0z.
- by rewrite (q_nat_cat n) ?subSnn ?q_nat1 ?mulr1.
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

(*Lemma prod_q_binom_pos a n x :
  q_binom_pos a n.+1 x = \prod_(0 <= i < n.+1) (x -  q ^ i * a).
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
    by rewrite q_nat0 addrK' Num.Theory.normr0.
  - exists (e / n%:R).
Admitted. *)

(* q-derivative of x ^ n *)
Lemma Dq_pow n x :
  x != 0 -> Dq (fun x => x ^ n) x = q_nat n * x ^ (n - 1).
Proof.
  move=> Hx.
  rewrite /Dq /dq /q_nat.
  rewrite -{4}(mul1r x) -mulrBl expfzMl -add_div; last first.
    by apply mulf_neq0.
  rewrite [in x ^ n](_ : n = (n -1) +1) //; last first.
    by rewrite subrK.
  rewrite expfzDr ?expr1z ?mulrA -?mulNr ?red_frac_r ?add_div //.
  rewrite -{2}[x ^ (n - 1)]mul1r -mulrBl mulrC mulrA.
  by rewrite [in (q - 1)^-1 * (q ^ n - 1)] mulrC.
Qed.

(* q-derivative product rule *)
Lemma Dq_prod f g x : x != 0 ->
  Dq (f ** g) x = f (q * x) * Dq g x + (g x) * Dq f x.
Proof.
  move=> Hx.
  rewrite /Dq dq_prod -add_div.
    by rewrite !mulrA.
  by apply denom_is_nonzero.
Qed.

(* q-derivative product rule' *)
Lemma Dq_prod' f g x : x != 0 ->
   Dq (f ** g) x = (f x) * Dq g x + g (q * x) * Dq f x.
Proof.
  move=> Hx.
  by rewrite (mulfC _ f g) Dq_prod // addrC.
Qed.

(* reduce fraction in q-derivative *)
Lemma Dq_divff f g x : g x != 0 -> g (q * x) != 0 ->
  Dq (g ** (f // g)) x = Dq f x.
Proof.
  move=> Hgx Hgqx.
  rewrite /Dq /dq.
  rewrite [f (q * x) / g (q * x)] mulrC.
  rewrite [f x / g x] mulrC.
  by rewrite !mulrA !divff // !mul1r.
Qed.

(* q-derivative quotient rule *)
Lemma Dq_quot f g x : x != 0 -> g x != 0 -> g (q * x) != 0 ->
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
    rewrite -Dq_prod //.
    by apply Dq_divff.
  by apply mulf_neq0.
Qed.

(* q-derivative quotient rule' *)
Lemma Dq_quot' f g x : x != 0 ->
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
    rewrite -Dq_prod' //.
    by apply Dq_divff.
  by apply mulf_neq0.
Qed.

(* q-analogue of polynomial for nat *)
Fixpoint q_binom_pos a n x :=
  match n with
  | 0 => 1
  | n.+1 => (q_binom_pos a n x) * (x - q ^ n * a)
  end.

Fixpoint q_binom_pos_poly a n :=
  match n with
  | 0 => 1
  | n.+1 => (q_binom_pos_poly a n) * ('X - (q ^ n * a)%:P)
  end.

Lemma q_binom_size a n : size (q_binom_pos_poly a n) = n.+1.
Proof.
  elim: n => [|n IH] => //=.
  - by rewrite size_poly1.
  - rewrite size_Mmonic.
        by rewrite IH size_XsubC addn2.
      by rewrite -size_poly_gt0 IH.
    by apply monicXsubC.
Qed.

Lemma q_binom_posE a n x :
  q_binom_pos a n x = (q_binom_pos_poly a n).[x].
Proof.
  elim: n => [|n IH] //=.
  - by rewrite hornerC.
  - by rewrite hornerM -IH hornerXsubC.
Qed.

Lemma q_binom_pos_head a n x:
   q_binom_pos a n.+1 x =
  (x - a) * q_binom_pos (q * a) n x.
Proof.
  elim: n => [|n IH] /=.
  - by rewrite expr0z !mul1r mulr1.
  - by rewrite !mulrA -IH exprSzr.
Qed.

Lemma q_binomxa a n : q_binom_pos a n.+1 a = 0.
Proof. by rewrite q_binom_pos_head addrK' mul0r. Qed.

Lemma q_binomx0 a n :
  q_binom_pos (- a) n 0 = q ^+((n * (n - 1))./2) * a ^+ n.
Proof.
  elim: n => [| n IH] //.
  - by rewrite mul0n /= expr0 mulr1.
  - destruct n.
      by rewrite /= !mul1r sub0r opp_oppE expr1.
    case Hq0 : (q == 0).
    + rewrite q_binom_pos_head.
      destruct n.
        rewrite /= expr0z.
        move: Hq0 => /eqP ->.
        by rewrite opp_oppE add0r mul1r expr1 sub0r !mul0r mul1r oppr0 mulr0.
      rewrite q_binom_pos_head.
      move: Hq0 => /eqP ->.
      rewrite mul0r subr0 mulrA !mulr0 !mul0r.
      have -> : (n.+3 * (n.+3 - 1))./2 =
                ((n.+3 * (n.+3 - 1))./2 - 1)%N.+1.
        by rewrite -[RHS]addn1 subnK.
      by rewrite expr0n mul0r.
    + rewrite /= in IH.
      rewrite [LHS] /= IH // sub0r -mulrN opp_oppE.
      rewrite [q ^ n.+1 * a] mulrC.
      rewrite mulrA mulrC 2!mulrA -exprD.
      have -> : (n.+1 + (n.+1 * (n.+1 - 1))./2 =
                (n.+2 * (n.+2 - 1))./2)%N.
        by rewrite !subn1 /= half_add.
      by rewrite -mulrA -(exprSzr a n.+1).
Qed.

(*Lemma prod_q_binom_pos a n x :
  q_binom_pos a n.+1 x = \prod_(0 <= i < n.+1) (x -  q ^ i * a).
Proof.
  elim: n => [/=|n IH].
  - by rewrite big_nat1 mul1r.
  - rewrite (@big_cat_nat _ _ _ n.+1) //=.
    by rewrite big_nat1 -IH.
Qed.*)

(* q-derivative of q-polynomial for nat *)
Theorem Dq_q_binom_pos a n x : x != 0 ->
  Dq (q_binom_pos a n.+1) x =
  q_nat n.+1 * q_binom_pos a n x.
Proof.
  move=> Hx.
  elim: n => [|n IH].
  - rewrite /Dq /dq /q_binom_pos /q_nat.
    rewrite !mul1r mulr1 expr1z.
    rewrite opprB subrKA !divff //.
    by rewrite denom_is_nonzero.
  - rewrite (_ : Dq (q_binom_pos a n.+2) x =
                 Dq ((q_binom_pos a n.+1) **
                 (fun x => (x - q ^ (n.+1) * a))) x) //.
    rewrite Dq_prod' //.
    rewrite [Dq (+%R^~ (- (q ^ n.+1 * a))) x] /Dq /dq.
    rewrite opprB subrKA divff //.
      rewrite mulr1 exprSz.
      rewrite -[q * q ^ n * a] mulrA -(mulrBr q) IH.
      rewrite -[q * (x - q ^ n * a) * (q_nat n.+1 * q_binom_pos a n x)] mulrA.
      rewrite [(x - q ^ n * a) * (q_nat n.+1 * q_binom_pos a n x)] mulrC.
      rewrite -[q_nat n.+1 * q_binom_pos a n x * (x - q ^ n * a)] mulrA.
      rewrite (_ : q_binom_pos a n x * (x - q ^ n * a) = q_binom_pos a n.+1 x) //.
      rewrite mulrA.
      rewrite -{1}(mul1r (q_binom_pos a n.+1 x)).
      by rewrite -mulrDl -q_nat_cat1.
    by apply denom_is_nonzero.
Qed.

(* q-polynomial exponential law for nat *)
Lemma q_binom_pos_explaw x a m n :
  q_binom_pos a (m + n) x =
    q_binom_pos a m x * q_binom_pos (q ^ m * a) n x.
Proof.
  elim: n.
  - by rewrite addn0 /= mulr1.
  - elim => [_|n _ IH].
    + by rewrite addnS /= addn0 expr0z !mul1r.
    + rewrite addnS [LHS]/= IH /= !mulrA.
      by rewrite -[q ^ n.+1 * q ^ m] expfz_n0addr // addnC.
Qed.

Lemma q_binom_exp_non0l x a m n :
  q_binom_pos a (m + n) x != 0 -> q_binom_pos a m x != 0.
Proof.
  rewrite q_binom_pos_explaw.
  by apply mulnon0.
Qed.

Lemma q_binom_exp_non0r x a m n :
  q_binom_pos a (m + n) x != 0 -> q_binom_pos (q ^ m * a) n x != 0.
Proof.
  rewrite q_binom_pos_explaw mulrC.
  by apply mulnon0.
Qed.

(* q-polynomial for neg *)
Definition q_binom_neg a n x := 1 / q_binom_pos (q ^ ((Negz n) + 1) * a) n x.

(* q-poly_nat 0 = q-poly_neg 0 *)
Lemma q_binom_0 a x : q_binom_neg a 0 x = q_binom_pos a 0 x.
Proof.
  by rewrite /q_binom_neg /= -[RHS] (@divff _ 1) //.
Qed.

Theorem q_binom_neg_inv a n x :
  q_binom_pos (q ^ (Negz n + 1) * a) n x != 0 ->
  q_binom_neg a n x * q_binom_pos (q ^ (Negz n + 1) * a) n x = 1.
Proof.
  move=> H.
  by rewrite /q_binom_neg mulrC mulrA mulr1 divff.
Qed.

(* q-analogue polynomial for int *)
Definition q_binom a n x :=
  match n with
  | Posz n0 => q_binom_pos a n0 x
  | Negz n0 => q_binom_neg a n0.+1 x
  end.

Definition q_binom_denom a n x := match n with
  | Posz n0 => 1
  | Negz n0 => q_binom_pos (q ^ Negz n0 * a) n0.+1 x
  end.

Lemma Dq_q_binom_int_to_neg a n x :
  Dq (q_binom a (Negz n)) x = Dq (q_binom_neg a (n + 1)) x.
Proof. by rewrite /Dq /dq /= addn1. Qed.

Lemma q_binom_exp_0 a m n x : m = 0 \/ n = 0 ->
  q_binom a (m + n) x = q_binom a m x * q_binom (q ^ m * a) n x.
Proof.
  move=> [->|->].
  - by rewrite add0r expr0z /= !mul1r.
  - by rewrite addr0 /= mulr1.
Qed.

Lemma q_binom_exp_pos_neg a (m n : nat) x : q != 0 ->
  q_binom_pos (q ^ (Posz m + Negz n) * a) n.+1 x != 0 ->
  q_binom a (Posz m + Negz n) x = q_binom a m x * q_binom (q ^ m * a) (Negz n) x.
Proof.
  move=> Hq0 Hq_binommn.
  case Hmn : (Posz m + Negz n) => [l|l]  /=.
  - rewrite /q_binom_neg mul1r.
    rewrite (_ : q_binom_pos a m x = q_binom_pos a (l + n.+1) x).
      rewrite q_binom_pos_explaw.
      have -> : q ^ (Negz n.+1 + 1) * (q ^ m * a) = q ^ l * a.
        by rewrite mulrA -expfzDr // -addn1 Negz_addK addrC Hmn.
      rewrite -{2}(mul1r (q_binom_pos (q ^ l * a) n.+1 x)).
      rewrite red_frac_r.
        by rewrite divr1.
      by rewrite -Hmn.
    apply Negz_transp in Hmn.
    apply (eq_int_to_nat R) in Hmn.
    by rewrite Hmn.
  - rewrite /q_binom_neg.
    have Hmn' : n.+1 = (l.+1 + m)%N.
      move /Negz_transp /esym in Hmn.
      rewrite addrC in Hmn.
      move /Negz_transp /(eq_int_to_nat R) in Hmn.
      by rewrite addnC in Hmn.
    rewrite (_ : q_binom_pos (q ^ (Negz n.+1 + 1) * (q ^ m * a)) n.+1 x 
               = q_binom_pos (q ^ (Negz n.+1 + 1) * (q ^ m * a))
                              (l.+1 + m) x).
      rewrite q_binom_pos_explaw.
      have -> : q ^ (Negz n.+1 + 1) * (q ^ m * a) =
                q ^ (Negz l.+1 + 1) * a.
        by rewrite mulrA -expfzDr // !NegzS addrC Hmn.
      have -> : q ^ l.+1 * (q ^ (Negz l.+1 + 1) * a) = a.
        by rewrite mulrA -expfzDr // NegzS NegzK expr0z mul1r.
      rewrite mulrA.
      rewrite [q_binom_pos (q ^ (Negz l.+1 + 1) * a) l.+1 x *
               q_binom_pos a m x] mulrC.
      rewrite red_frac_l //.
      have -> : a = q ^ l.+1 * (q ^ (Posz m + Negz n) * a) => //.
        by rewrite mulrA -expfzDr // Hmn NegzK expr0z mul1r.
      apply q_binom_exp_non0r.
      rewrite -Hmn' //.
    by rewrite Hmn'.
Qed.

Lemma q_binom_exp_neg_pos a m n x : q != 0 ->
  q_binom_pos (q ^ Negz m * a) m.+1 x != 0 ->
  q_binom a (Negz m + Posz n) x =
  q_binom a (Negz m) x * q_binom (q ^ Negz m * a) n x.
Proof.
  move=> Hq0 Hq_binomm.
  case Hmn : (Negz m + n) => [l|l] /=.
  - rewrite /q_binom_neg.
    rewrite (_ : q_binom_pos (q ^ Negz m * a) n x =
                 q_binom_pos (q ^ Negz m * a)
                   (m.+1 + l) x).
      rewrite q_binom_pos_explaw.
      have -> : q ^ (Negz m.+1 + 1) * a = q ^ Negz m * a.
        by rewrite -addn1 Negz_addK.
      have -> : q ^ m.+1 * (q ^ Negz m * a) = a.
        by rewrite mulrA -expfzDr // NegzK expr0z mul1r.
      rewrite mulrC mulrA mulr1.
      rewrite -{2}[q_binom_pos (q ^ Negz m * a) m.+1 x]
                    mulr1.
      rewrite red_frac_l //.
      by rewrite divr1.
    move: Hmn.
    rewrite addrC.
    move /Negz_transp /eq_int_to_nat.
    by rewrite addnC => ->.
  - rewrite /q_binom_neg.
    have Hmn' : m.+1 = (n + l.+1)%N.
      rewrite addrC in Hmn.
      move /Negz_transp /esym in Hmn.
      rewrite addrC in Hmn.
      by move /Negz_transp /(eq_int_to_nat R) in Hmn.
    rewrite {2}Hmn'.
    rewrite q_binom_pos_explaw.
    have -> : q ^ n * (q ^ (Negz m.+1 + 1) * a) =
                q ^ (Negz l.+1 + 1) * a.
      by rewrite mulrA -expfzDr // !NegzS addrC Hmn.
    have -> : q ^ (Negz m.+1 + 1) * a = q ^ Negz m * a.
      by rewrite NegzS.
    rewrite [RHS] mulrC mulrA red_frac_l //.
    apply (@q_binom_exp_non0l x _ n l.+1).
    by rewrite -Hmn'.
Qed.

Lemma q_binom_exp_neg_neg a m n x : q != 0 ->
  q_binom a (Negz m + Negz n) x =
  q_binom a (Negz m) x * q_binom (q ^ Negz m * a) (Negz n) x .
Proof.
  move=> Hq0 /=.
  rewrite /q_binom_neg.
  have -> : (m + n).+2 = ((n.+1) + (m.+1))%N.
    by rewrite addnC addnS -addn2.
  rewrite q_binom_pos_explaw.
  have -> : q ^ n.+1 * (q ^ (Negz (n.+1 + m.+1) + 1) * a) =
              q ^ (Negz m.+1 + 1) * a.
    rewrite mulrA -expfzDr //.
    have -> : Posz n.+1 + (Negz (n.+1 + m.+1) + 1) = Negz m.+1 + 1 => //.
    by rewrite Negz_add 2!addrA NegzK add0r.
  have -> : (q ^ (Negz n.+1 + 1) * (q ^ Negz m * a)) =
              (q ^ (Negz (n.+1 + m.+1) + 1) * a).
    by rewrite mulrA -expfzDr // NegzS -Negz_add addnS NegzS.
  rewrite mulf_div mulr1.
  by rewrite [q_binom_pos (q ^ (Negz (n.+1 + m.+1) + 1) * a) n.+1 x *
            q_binom_pos (q ^ (Negz m.+1 + 1) * a) m.+1 x] mulrC.
Qed.

Theorem q_binom_exp_law a m n x : q != 0 ->
  q_binom_denom a m x != 0 ->
  q_binom_denom (q ^ m * a) n x != 0 ->
  q_binom a (m + n) x = q_binom a m x * q_binom (q ^ m * a) n x.
Proof.
  move=> Hq0.
  case: m => m Hm.
  - case: n => n Hn.
    + by apply q_binom_pos_explaw.
    + rewrite q_binom_exp_pos_neg //.
      by rewrite addrC expfzDr // -mulrA.
  - case: n => n Hn.
    + by rewrite q_binom_exp_neg_pos.
    + by apply q_binom_exp_neg_neg.
Qed.

(* q-derivative of q-polynomial for 0 *)
Lemma Dq_q_binomn0 a x :
  Dq (q_binom a 0) x = q_nat 0 * q_binom a (- 1) x.
Proof. by rewrite Dq_const q_nat0 mul0r. Qed.

Lemma q_binom_qx a m n x : q != 0 ->
  q_binom_pos (q ^ m * a) n (q * x) =
    q ^ n * q_binom_pos (q ^ (m - 1) * a) n x.
Proof.
  move=> Hq0.
  elim: n => [|n IH] /=.
  - by rewrite expr0z mul1r.
  - rewrite IH.
    rewrite exprSzr -[RHS]mulrA.
    rewrite [q * (q_binom_pos (q ^ (m - 1) * a) n x *
              (x - q ^ n * (q ^ (m - 1) * a)))] mulrA.
    rewrite [q * q_binom_pos (q ^ (m - 1) * a) n x] mulrC.
    rewrite -[q_binom_pos (q ^ (m - 1) * a) n x * q *
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
Theorem Dq_q_binom_neg a n x : q != 0 -> x != 0 ->
  (x - q ^ (Negz n) * a) != 0 ->
  q_binom_pos (q ^ (Negz n + 1) * a) n x != 0 ->
  Dq (q_binom_neg a n) x = q_nat (Negz n + 1) * q_binom_neg a (n.+1) x.
Proof.
  move=> Hq0 Hx Hqn Hq_binom.
  destruct n.
  - by rewrite /Dq /dq /q_binom_neg /= addrK' q_nat0 !mul0r.
  - rewrite Dq_quot //.
      rewrite Dq_const mulr0 mul1r sub0r.
      rewrite Dq_q_binom_pos // q_binom_qx // -mulNr.
      rewrite [q_binom_pos (q ^ (Negz n.+1 + 1) * a) n.+1 x *
                (q ^ n.+1 * q_binom_pos (q ^ (Negz n.+1 + 1 - 1) *
                  a) n.+1 x)] mulrC.
      rewrite -mulf_div.
      have -> : q_binom_pos (q ^ (Negz n.+1 + 1) * a) n x /
                    q_binom_pos (q ^ (Negz n.+1 + 1) * a) n.+1 x =
                      1 / (x - q ^ (- 1) * a).
        rewrite -(mulr1
                     (q_binom_pos (q ^ (Negz n.+1 + 1) * a) n x)) /=.
        rewrite red_frac_l.
          rewrite NegzE mulrA -expfzDr // addrA -addn2.
          rewrite (_ : Posz (n + 2)%N = Posz n + 2) //.
          rewrite -{1}(add0r (Posz n)).
          by rewrite addrKA.
        by rewrite /=; apply mulnon0 in Hq_binom.
      rewrite mulf_div.
      rewrite -[q ^ n.+1 *
                 q_binom_pos (q ^ (Negz n.+1 + 1 - 1) * a) n.+1 x *
                   (x - q ^ (-1) * a)]mulrA.
      have -> : q_binom_pos (q ^ (Negz n.+1 + 1 - 1) * a) n.+1 x *
                (x - q ^ (-1) * a) =
                q_binom_pos (q ^ (Negz (n.+1)) * a) n.+2 x => /=.
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
      rewrite /q_binom_neg /=.
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
    rewrite q_binom_qx // mulf_neq0 //.
      by rewrite expnon0.
    rewrite q_binom_pos_head mulf_neq0 //.
    rewrite (_ : Negz n.+1 + 1 - 1 = Negz n.+1) //.
      by rewrite addrK.
    move: Hq_binom => /=.
    move/mulnon0.
    by rewrite addrK mulrA -{2}(expr1z q) -expfzDr.
Qed.

Theorem Dq_q_binom a n x : q != 0 -> x != 0 ->
  x - q ^ (n - 1) * a != 0 ->
  q_binom (q ^ n * a) (- n) x != 0 ->
  Dq (q_binom a n) x = q_nat n * q_binom a (n - 1) x.
Proof.
  move=> Hq0 Hx Hxqa Hq_binom.
  case: n Hxqa Hq_binom => [|/=] n Hxqa Hq_binom.
  - destruct n.
    + by rewrite Dq_q_binomn0.
    + rewrite Dq_q_binom_pos //.
      rewrite (_ : Posz n.+1 - 1 = n) //.
      rewrite -addn1.
      rewrite (_ : Posz (n + 1)%N = Posz n + 1) //.
      by rewrite addrK.
  - rewrite Dq_q_binom_int_to_neg Dq_q_binom_neg //.
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

Lemma q_bicoefn0 n : q_fact n != 0 -> q_bicoef n 0 = 1.
Proof.
move=> H.
by rewrite /q_bicoef /= mul1r subn0 divff.
Qed.

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

Lemma q_bicoef_compute n j : q_fact n != 0 -> (j < n)%N ->
  q_bicoef n j * q_fact j * q_nat (n - j.+1).+1 =
  q_bicoef n j.+1 * (q_fact j * q_nat j.+1).
Proof.
move=> Hfact Hj.
  rewrite (mulrC (q_bicoef n j)) -mulrA mulrC.
  rewrite (mulrC (q_fact j)) [RHS]mulrA.
  f_equal.
  rewrite /q_bicoef.
  rewrite -mulrA -[RHS]mulrA.
  f_equal => /=.
  rewrite mulrC subnSK //.
  have -> : q_fact (n - j) = q_fact (n - j.+1) * q_nat (n - j)%N.
    by rewrite -(subnSK Hj) /=.
  rewrite mulrA -{1}(mul1r (q_nat (n - j)%N)) red_frac_r; last first.
    rewrite -(subnSK Hj).
    apply q_fact_nat_non0.
    apply (q_fact_lenon0 _ j).
    rewrite subnSK //.
    rewrite subnK //.
    by apply ltnW.
  rewrite [RHS]mulrC.
  rewrite [q_fact j * q_nat j.+1]mulrC.
  rewrite -{1}(mulr1 (q_nat j.+1)).
  rewrite -[q_nat j.+1 * q_fact j * q_fact (n - j.+1)]mulrA.
  rewrite red_frac_l //.
  apply q_fact_nat_non0.
  apply (q_fact_lenon0 _ (n - j.+1)%N).
  by rewrite subnKC.
Qed.

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

Definition polyderiv (D : (R -> R) -> (R -> R)) (p : {poly R}) :=
  D (fun (x : R) => p.[x]).

Lemma poly_happly p p' (x : R) : p = p' -> p.[x] = p'.[x].
Proof. by move=> ->. Qed.

Lemma polyX_div n : (polyX R) ^ n.+1 %/ (polyX R) = (polyX R) ^ n.
Proof.
by rewrite exprSzr mulpK ?polyX_eq0.
Qed.

Notation "D # p" := (polyderiv D p) (at level 49).

Definition scaleq (p : {poly R}):= \poly_(i < size p) (q ^ i * p`_i).

Lemma scaleq_scale a p : scaleq (a *: p) = a *: scaleq p.
Proof.
rewrite /scaleq; apply polyP => j.
case Ha : (a == 0).
- move/eqP : Ha ->; rewrite !scale0r.
  by rewrite coef_poly size_poly0 //= coef0.
- have Ha' : a != 0 by rewrite Ha.
  rewrite size_scale // coefZ !coef_poly.
  case : (j < size p)%N.
  + by rewrite -scalerAr coefZ.
  + by rewrite mulr0.
Qed.

Lemma scaleqC c : scaleq c%:P = c%:P.
Proof.
rewrite /scaleq poly_def.
rewrite (sumW _ (fun i => (q ^ i * c%:P`_i) *: 'X^i)) size_polyC.
case Hc : (c == 0) => /=.
- rewrite big_nil.
  by move /eqP : Hc ->.
- by rewrite big_nat1 expr0z mul1r coefC /= -mul_polyC mulr1.
Qed.

(* Lemma scaleq0 : scaleq 0 = 0.
Proof. by rewrite -{1}(scale0r 0) scaleq_scale scale0r. Qed. *)

Lemma scaleq_add p p' : scaleq (p + p') = scaleq p + scaleq p'.
Proof.
rewrite /scaleq.
  rewrite (polyW' R (p + p') (maxn (size p) (size p'))); last first.
    by apply size_add.
  rewrite (polyW' R p (maxn (size p) (size p'))); last first.
    by apply leq_maxl.
  rewrite (polyW' R p' (maxn (size p) (size p'))); last first.
    by apply leq_maxr.
  rewrite sum_add.
  by under eq_bigr do rewrite coefD mulrDr scalerDl.
Qed.

Lemma scaleq_prodX p : scaleq ('X * p) = scaleq 'X * scaleq p.
Proof.
case Hp : (p == 0).
  move /eqP : Hp ->.
  by rewrite mulr0 scaleqC mulr0.
rewrite /scaleq !poly_def.
rewrite (sumW _ (fun i => (q ^ i * ('X * p)`_i) *: 'X^i)).
rewrite (sumW _ (fun i => (q ^ i * 'X`_i) *: 'X^i)).
rewrite (sumW _ (fun i => (q ^ i * p`_i) *: 'X^i)).
rewrite size_polyX.
rewrite (@big_cat_nat  _ _ _ 1 _ 2) //= !big_nat1.
rewrite !coefX /= mulr0 scale0r add0r expr1z mulr1.
rewrite -sum_distr.
have -> : size ('X * p) = (size p).+1.
  by rewrite mulrC size_mulX ?Hp.
rewrite (@big_cat_nat _ _ _ 1) //= !big_nat1.
rewrite coefXM /= mulr0 scale0r add0r.
have -> : (1 = 0 + 1)%N by [].
rewrite big_addn subn1 /=.
under eq_big_nat => i /andP [] _ Hi.
  rewrite coefXM addn1 /= exprSzr -mulrA [q * p`_i]mulrC mulrA.
  rewrite -scalerA exprSr scalerAr -{2}(expr1 'X) -(add0n 1%N) scalerAl.
over.
done.
Qed.

Lemma scaleq_prod (p p' : {poly R}) n : (size p <= n)%N ->
  scaleq (p * p') = scaleq p * scaleq p'.
Proof.
have Hp0 : forall (p : {poly R}), size p = 0%N ->
  scaleq (p * p') = scaleq p * scaleq p'.
  move=> p0.
  move/eqP.
  rewrite size_poly_eq0.
  move/eqP ->.
  by rewrite mul0r scaleqC mul0r.
elim: n p => [|n IH] p Hsize.
  move: Hsize.
  rewrite leqn0 => /eqP.
  by apply Hp0.
case Hp : (size p == 0%N).
  rewrite Hp0 //.
  by apply/eqP.
have -> : p = p - (p`_0)%:P + (p`_0)%:P by rewrite subrK.
set p1 := (\poly_(i < (size p).-1) p`_i.+1).
have -> : p - (p`_0)%:P = 'X * p1.
  rewrite -{1}(coefK p) poly_def.
  rewrite (sumW _ (fun i => p`_i *: 'X^i)).
  rewrite (@big_cat_nat _ _ _ 1) //=; last first.
    by apply neq0_lt0n.
  rewrite big_nat1 -mul_polyC mulr1 (addrC (p`_0)%:P) addrK.
  have -> : (1 = 0 + 1)%N by [].
  rewrite big_addn subn1.
  under eq_bigr do rewrite addn1 exprSr scalerAl.
  by rewrite sum_distr /p1 poly_def -sumW.
rewrite mulrDl [LHS]scaleq_add mul_polyC scaleq_scale -mulrA scaleq_prodX.
have -> : scaleq (p1 * p') = scaleq p1 * scaleq p'.
  rewrite IH //.
  apply (@leq_trans (size p).-1).
    apply size_poly.
  rewrite -(leq_add2r 1).
  have -> : ((size p).-1 + 1 = size p)%N.
    rewrite addn1 prednK //.
    by apply neq0_lt0n.
  by rewrite addn1.
by rewrite mulrA -scaleq_prodX -mul_polyC -mulrDl -{1}scaleqC -scaleq_add.
Qed.

Lemma scale_constpoly (a c : R) : a *: c%:P = (a * c)%:P.
Proof.
apply polyP => i.
rewrite coefZ !coefC.
case : (i == 0%N) => //.
by rewrite mulr0.
Qed.

Lemma scaleqX a : scaleq ('X - a%:P) = q *: 'X - a%:P.
Proof.
rewrite /scaleq poly_def size_XsubC.
rewrite (sumW _ (fun i => (q ^ i * ('X - a%:P)`_i) *: 'X^i)).
rewrite (@big_cat_nat _ _ _ 1) //= !big_nat1.
rewrite addrC expr1z expr0z !coefB !coefX !coefC /=.
by rewrite subr0 sub0r mulrN mulr1 mul1r scale_constpoly mulr1 polyCN.
Qed.

Lemma scaleqXn n : scaleq ('X ^+ n) = (q ^ n) *: 'X ^+ n.
Proof.
rewrite /scaleq poly_def size_polyXn.
rewrite (sumW _ (fun i => (q ^ i * 'X^n`_i) *: 'X^i)).
rewrite (@big_cat_nat _ _ _ n) //= big_nat1 coefXn.
have -> : (eq_op n n) => //=.
rewrite mulr1.
under eq_big_nat => i /andP [] _ Hi.
  rewrite coefXn.
  have -> : (eq_op i n) = false => /=.
  by apply ltn_eqF.
  rewrite -mul_polyC mulr0 polyC0 mul0r.
over.
by rewrite big1 ?add0r.
Qed.

Definition dq_f p := scaleq p - p.

(* should be tools *)
Lemma size_N0_lt (p : {poly R}) : (size p == 0%N) = false -> (0 < size p)%N.
Proof.
move=> Hsize.
rewrite ltn_neqAle.
apply /andP; split => //.
move: Hsize.
by rewrite eq_sym => ->.
Qed.

Lemma dq_fpXE p : dq_f p = 'X * \poly_(i < size p) ((q ^ i.+1 - 1) * p`_i.+1).
Proof.
rewrite /dq_f /scaleq.
rewrite -{3}(coefK p).
rewrite !poly_def.
rewrite (sumW _ (fun i => (q ^ i * p`_i) *: 'X^i)).
rewrite (sumW _ (fun i => (p`_i *: 'X^i))).
rewrite (sumW _ (fun i => (((q ^ i.+1 - 1) * p`_i.+1) *: 'X^i))).
rewrite sum_sub.
case Hsize : (size p == 0%N).
- move /eqP : Hsize ->.
  by rewrite !big_nil mulr0.
- rewrite (@big_cat_nat _ _ _ 1) //=; last first.
    by apply size_N0_lt.
  rewrite big_nat1 expr0z mul1r addrK' add0r.
  have -> : (1 = 0 + 1)%N by [].
  rewrite big_addn -sum_distr.
  rewrite [RHS](@big_cat_nat _ _ _ (size p - 1)) //=; last first.
    by rewrite subn1 leq_pred.
  have {4}-> : size p = ((size p) - 1).+1.
    rewrite subn1 prednK //.
    by apply size_N0_lt.
  rewrite big_nat1.
  have -> : p`_(size p - 1).+1 = 0.
    rewrite subn1 prednK //.
      by apply /(leq_sizeP _ (size p)) => //=.
    by apply size_N0_lt.
  rewrite mulr0 scale0r mul0r addr0.
  under eq_bigr => i _.
    rewrite -scalerBl addn1 -{2}(mul1r p`_i.+1) -mulrBl exprSr scalerAl.
  over.
  by move=> /=.
Qed.

Lemma dq_f_prod' p p' : dq_f (p * p') = p * dq_f p' + scaleq p' * dq_f p.
Proof.
rewrite /dq_f.
rewrite (scaleq_prod _ _ (size p)) // !mulrBr [RHS]addrC addrA.
f_equal.
rewrite -addrA [- (scaleq p' * p) + p * scaleq p']addrC.
by rewrite [p * scaleq p']mulrC addrK' addr0 mulrC.
Qed.

Lemma dq_fXE : dq_f 'X = (q - 1) *: 'X.
Proof.
rewrite /dq_f /scaleq.
rewrite poly_def size_polyX.
rewrite (sumW _ (fun i => (q ^ i * 'X`_i) *: 'X^i)).
rewrite (@big_cat_nat _ _ _ 1) //= !big_nat1.
rewrite !coefX /=.
by rewrite mulr0 scale0r add0r expr1z mulr1 scalerBl scale1r.
Qed.

Lemma dq_f_dqE p x : (dq_f p).[x] = (dq # p) x.
Proof.
rewrite /dq_f /scaleq /(_ # _) /dq.
rewrite hornerD hornerN.
f_equal.
rewrite -{3}(coefK p).
rewrite !horner_poly.
have -> : \sum_(i < size p) q ^ i * p`_i * x ^+ i =
          \sum_(0 <= i < size p) q ^ i * p`_i * x ^+ i.
  by rewrite big_mkord.
rewrite (sumW _ (fun i => p`_i * (q * x) ^+ i)).
apply esym.
under eq_big_nat => i /andP [] Hi _.
  rewrite exprMn_comm ?mulrA ?[p`_i * q ^+ i]mulrC.
over.
  by rewrite /GRing.comm mulrC.
done.
Qed.

Definition Dq_f p := dq_f p %/ dq_f 'X.

Lemma Dq_f_ok p : dq_f 'X %| dq_f p.
Proof.
by rewrite dq_fXE dvdpZl ?dq_fpXE ?dvdp_mulIl.
Qed.

Lemma Dq_fE' p : Dq_f p = dq_f p %/ ((q - 1) *: 'X).
Proof. by rewrite /Dq_f dq_fXE. Qed.

Lemma Dq_f_prod' p p' : Dq_f (p * p') = p * Dq_f p' + scaleq p' * Dq_f p.
Proof.
rewrite /Dq_f !divp_mulA ?Dq_f_ok //.
by rewrite -divpD dq_f_prod'.
Qed.

(* should be tools *)
Lemma scale_div c d (p p' : {poly R}) : d != 0 ->
  (c *: p) %/ (d *: p') = (c / d) *: (p %/ p').
Proof.
move=> Hd.
by rewrite divpZl divpZr // scalerA.
Qed.

Lemma Dq_f_const c : Dq_f c%:P = 0%:P.
Proof.
rewrite /Dq_f.
have -> : dq_f c%:P = 0.
  rewrite /dq_f /scaleq poly_def size_polyC.
  rewrite (sumW _ (fun i => (q ^ i * c%:P`_i) *: 'X^i)).
  case Hc : (c != 0) => /=.
  - rewrite big_nat1.
    rewrite expr0z mul1r.
    have -> : 'X^0 = 1%:P by [].
    by rewrite coefC /= polyC1 alg_polyC addrK'.
  - rewrite big_nil.
    move: Hc.
    rewrite /(_ != 0) /=.
    case Hc : (c == 0) => //= _.
    move/ eqP : Hc ->.
    by rewrite polyC0 subr0.
  by rewrite div0p.
Qed.

(* should be tools *)
Lemma divpsum n P (d : {poly R}) :
  (\sum_(0 <= i < n) P i) %/ d = \sum_(0 <= i < n) (P i %/ d).
Proof.
elim: n => [|n IH].
- by rewrite !big_nil div0p.
- by rewrite !(@big_cat_nat _ _ _ n 0 n.+1) //= !big_nat1 divpD IH.
Qed.

Definition Dq' (p : {poly R}) := \poly_(i < size p) (q_nat (i.+1) * p`_i.+1).

Lemma Dq_f_Dq'E p : Dq_f p = Dq' p.
Proof.
case Hsize : (size p == 0%N).
- move: Hsize.
  rewrite size_poly_eq0 => /eqP ->.
  rewrite Dq_f_const.
  rewrite /Dq' poly_def.
  rewrite (sumW _ (fun i => (q_nat i.+1 * 0%:P`_i.+1) *: 'X^i)).
  by rewrite size_poly0 big_nil.
- rewrite Dq_fE' /dq_f /scaleq /Dq' -{3}(coefK p) !poly_def.
  rewrite (sumW _ (fun i => (q ^ i * p`_i) *: 'X^i)).
  rewrite (sumW _ (fun i => p`_i *: 'X^i)).
  rewrite (sumW _ (fun i => (q_nat i.+1 * p`_i.+1) *: 'X^i)).
  rewrite sum_sub.
  rewrite divpsum.
  under eq_bigr => i _.
    rewrite -scalerBl -{2}(mul1r p`_i) -mulrBl scale_div //.
    have -> : (q ^ i - 1) * p`_i / (q - 1) = (q ^ i - 1) / (q - 1) * p`_i.
      by rewrite -mulrA [p`_i / (q - 1)]mulrC mulrA.
    rewrite -/(q_nat i).
  over.
  move=> /=.
  rewrite (@big_cat_nat _ _ _ 1) //=; last first.
    by apply size_N0_lt.
  rewrite big_nat1 q_nat0 mul0r scale0r add0r.
  have -> : (1 = 0 + 1)%N by [].
  rewrite big_addn.
  under eq_bigr do rewrite addn1 polyX_div.
  rewrite (@big_cat_nat _ _ _ (size p - 1) 0 (size p)) //=; last first.
    by rewrite subn1 leq_pred.
  have {4}-> : size p = ((size p) - 1).+1.
    rewrite subn1 prednK //.
    by apply size_N0_lt.
  rewrite big_nat1.
  have -> : p`_(size p - 1).+1 = 0.
    rewrite subn1 prednK //.
      by apply /(leq_sizeP _ (size p)) => //=.
    by apply size_N0_lt.
  by rewrite mulr0 scale0r addr0.
Qed.

(* Lemma Dq'_DqE p x : (Dq' R q p).[x] = (Dq R q # p) x.
Proof.
by rewrite -Dq_fE -Dq_f_DqE.
Qed. *)

Lemma hoDq_f_Dq'E n p :
  (Dq_f \^ n) p = ((Dq' \^ n) p).
Proof.
  elim: n => [|n IH] //=.
  by rewrite Dq_f_Dq'E IH.
Qed.

Lemma Dq'_prod' p p' :
   Dq' (p * p') = p * Dq' p' + scaleq p' * Dq' p.
Proof. by rewrite -!Dq_f_Dq'E Dq_f_prod'. Qed.

Lemma Dq'_DqE p x : x != 0 -> (Dq' p).[x] = (Dq # p) x.
Proof.
  move=> Hx.
  rewrite /Dq' /(_ # _) /Dq /dq.
  rewrite horner_poly !horner_coef.
  rewrite (sumW _ (fun i => (q_nat i.+1 * p`_i.+1 * x ^+ i))).
  rewrite (sumW _ (fun i => p`_i * (q * x) ^+ i)).
  rewrite (sumW _ (fun i => p`_i * x ^+ i)). 
  rewrite sum_sub.
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

Lemma hoDq'_DqE p x n : q != 0 -> x != 0 ->
  ((Dq' \^ n) p).[x] = ((Dq \^ n) # p) x.
Proof.
  move=> Hq0 Hx.
  rewrite /(_ # _).
  elim: n x Hx => [|n IH] x Hx //=.
  rewrite Dq'_DqE // {2}/Dq /dq -!IH //.
  by apply mulf_neq0 => //.
Qed.

Lemma Dq'_islinear_add (p p' : {poly R}) : Dq' (p + p') = Dq' p + Dq' p'.
Proof.
  rewrite /Dq'.
  rewrite (polyW R (p + p') (maxn (size p) (size p'))); last first.
    by apply size_add.
  rewrite (polyW R p (maxn (size p) (size p'))); last first.
    by apply leq_maxl.
  rewrite (polyW R p' (maxn (size p) (size p'))); last first.
    by apply leq_maxr.
  rewrite sum_add.
  by under eq_bigr do rewrite coefD mulrDr scalerDl.
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

Lemma Dq'_const a : Dq' a%:P = 0.
Proof. by rewrite -Dq_f_Dq'E Dq_f_const. Qed.

Lemma Dq'X : Dq' 'X = 1%:P.
Proof.
rewrite /Dq' poly_def size_polyX.
rewrite (sumW _ (fun i => (q_nat i.+1 * 'X`_i.+1) *: 'X^i)).
rewrite (@big_cat_nat _ _ _ 1) //= !big_nat1.
by rewrite !coefX /= mulr0 scale0r !q_nat1 mulr1 scale1r addr0.
Qed.

Lemma Dq'Xsub a : Dq' ('X - a%:P) = 1%:P.
Proof.
by rewrite Dq'_islinear_add -polyCN Dq'_const addr0 Dq'X.
Qed.

Lemma Dq'_pow n : Dq' ('X^n.+1) = (q_nat n.+1) *: 'X^n.
Proof.
elim: n => [|n IH].
- by rewrite Dq'X q_nat1 scale1r.
- rewrite exprS Dq'_prod' IH Dq'X mulrC.
  rewrite -mul_polyC -mulrA mul_polyC -exprSzr.
  rewrite [scaleq ('X^n.+1) * 1%:P]mulrC.
  by rewrite mul_polyC scale1r scaleqXn -scalerDl -q_nat_catn.
Qed.

Lemma Dq'_q_binom_poly a n :
  Dq' (q_binom_pos_poly a n.+1) = (q_nat n.+1) *: (q_binom_pos_poly a n).
Proof.
elim: n => [|n IH].
- rewrite /q_binom_pos_poly.
  rewrite expr0z !mul1r /Dq'.
  rewrite poly_def.
  have -> : size ('X - a%:P) = 2%N.
    by rewrite size_XsubC.
  have -> : \sum_(i < 2) (q_nat i.+1 * ('X - a%:P)`_i.+1) *: 'X^i =
            \sum_(0 <= i < 2) (q_nat i.+1 * ('X - a%:P)`_i.+1) *: 'X^i.
    by rewrite big_mkord.
  rewrite (@big_cat_nat _ _ _ 1) //= !big_nat1.
  rewrite !coefB !coefC /= !subr0.
  by rewrite !coefX /= scale_constpoly !mulr1 mulr0 scale0r addr0 alg_polyC.
- have -> : q_binom_pos_poly a n.+2 =
            (q_binom_pos_poly a n.+1) * ('X - (q ^ n.+1 * a)%:P) by [].
  rewrite Dq'_prod' Dq'Xsub mulr1 scaleqX IH.
  rewrite exprSz -mulrA -scale_constpoly -scalerBr.
  rewrite -!mul_polyC mulrA mulrC23 -mulrA.
  rewrite [('X - (q ^ n * a)%:P) * q_binom_pos_poly a n]mulrC.
  rewrite -/(q_binom_pos_poly a n.+1).
  rewrite (mul_polyC q) scale_constpoly (mul_polyC (q * q_nat n.+1)).
  rewrite -{1}(scale1r (q_binom_pos_poly a n.+1)) -scalerDl.
  by rewrite mul_polyC -q_nat_cat1.
Qed.

Lemma Dq'_isfderiv a : (forall n, q_fact n != 0) ->
  isfderiv Dq' (fun i : nat => q_binom_pos_poly a i / (q_fact i)%:P).
Proof.
move=> Hqnat.
rewrite /isfderiv.
destruct n => //.
- have -> : (GRing.one (poly_ringType R) / 1%:P) = 1%:P.
    by rewrite polyCV mul1r invr1.
  rewrite /Dq' (polyW _ _ 1).
    rewrite big_nat1.
    by rewrite coefC /= mulr0 scale0r.
  by apply size_polyC_leq1.
- have -> : q_binom_pos_poly a n.+1 / (q_fact n.+1)%:P =
            (q_fact n.+1)^-1 *: q_binom_pos_poly a n.+1.
    by rewrite mulrC polyCV mul_polyC.
  rewrite Dq'_islinear_scale -mul_polyC mulrC.
  rewrite Dq'_q_binom_poly -mul_polyC.
  rewrite [(q_nat n.+1)%:P * q_binom_pos_poly a n]mulrC.
  rewrite -polyCV -mulrA.
  f_equal.
  rewrite polyCV mul_polyC.
  rewrite scale_constpoly /=.
  rewrite -{1}(mul1r (q_nat n.+1)).
  rewrite red_frac_r ?mul1r ?polyCV //.
  by apply q_fact_nat_non0.
Qed.

Theorem q_Taylorp n (f : {poly R}) c :
  (forall n, q_fact n != 0) ->
  size f = n.+1 ->
  f =
    \sum_(0 <= i < n.+1)
   ((Dq' \^ i) f).[c] *: (q_binom_pos_poly c i / (q_fact i)%:P).
Proof.
move=> Hfact Hsizef.
apply general_Taylor => //.
- by apply Dq'_islinear.
- by apply Dq'_isfderiv.
- by rewrite invr1 mulr1 hornerC.
- move=> m.
  by rewrite hornerM -q_binom_posE q_binomxa mul0r.
- move=> m.
  rewrite polyCV mulrC size_Cmul.
    by rewrite q_binom_size.
  by apply /invr_neq0.
Qed.

Theorem q_Taylor n (f : {poly R}) x c :
  q != 0 ->
  c != 0 ->
  (forall n, q_fact n != 0) ->
  size f = n.+1 ->
  f.[x] =  \sum_(0 <= i < n.+1)
             ((Dq \^ i) # f) c * q_binom_pos c i x / q_fact i.
Proof.
  move=> Hq0 Ha Hfact Hsf.
  under eq_bigr do rewrite q_binom_posE.
  rewrite sum_poly_div.
  under eq_bigr do rewrite -hornerZ.
  rewrite -hornersumD.
  apply poly_happly.
  under eq_bigr do rewrite -hoDq'_DqE //.
  by apply q_Taylorp.
Qed.

Lemma hoDq'_pow n j : q_fact n != 0 -> (j <= n)%N ->
  (Dq' \^ j) 'X^n = (q_bicoef n j * q_fact j) *: 'X^(n - j).
Proof.
move=> Hn.
elim: j => [|j IH] Hj /=.
- by rewrite q_bicoefn0 ?mul1r ?scale1r ?subn0.
- rewrite IH; last first.
    by apply ltnW.
  rewrite Dq'_islinear_scale.
  have -> : (n - j = (n - j.+1).+1)%N by rewrite subnSK.
  rewrite Dq'_pow -mul_polyC -mul_polyC mulrA -[RHS]mul_polyC.
  f_equal.
  rewrite mul_polyC scale_constpoly.
  f_equal.
  by rewrite q_bicoef_compute //.
Qed.

Lemma hoDq'_pow1 n j : q_fact n != 0 -> (j <= n)%N ->
  ((Dq' \^ j) 'X^n).[1] = (q_bicoef n j * q_fact j).
Proof.
move=> Hn Hj.
by rewrite hoDq'_pow // hornerZ hornerXn expr1n mulr1.
Qed.

Lemma q_Taylorp_pow n : (forall n, q_fact n != 0) ->
  'X^n = \sum_(0 <= i < n.+1) (q_bicoef n i *: q_binom_pos_poly 1 i).
Proof.
move=> Hfact.
rewrite (q_Taylorp n 'X^n 1) //; last first.
  by rewrite size_polyXn.
under eq_big_nat => i /andP [_ Hi].
  rewrite hoDq'_pow1 //.
  rewrite [(q_binom_pos_poly 1 i / (q_fact i)%:P)]mulrC.
  rewrite polyCV scalerAl scale_constpoly -mulrA divff //.
  rewrite mulr1 mul_polyC.
over.
done.
Qed.

(* Lemma q_Taylor_pow x n : (forall n, q_fact n != 0) ->
  x ^+ n = \sum_(0 <= i < n.+1) (q_bicoef n i * q_binom_pos 1 i x). *)

Lemma hoDq'_q_binom n j a : q_fact n != 0 -> (j <= n)%N ->
  (Dq' \^ j) (q_binom_pos_poly (- a) n) =
  (q_bicoef n j * q_fact j) *: (q_binom_pos_poly (-a) (n - j)).
Proof.
move=> Hfact.
elim: j => [|j IH] Hj /=.
- by rewrite subn0 q_bicoefn0 ?mulr1 ?scale1r.
- rewrite IH; last first.
    by apply ltnW.
  rewrite Dq'_islinear_scale.
  have -> : (n - j = (n - j.+1).+1)%N by rewrite subnSK.
  rewrite Dq'_q_binom_poly -mul_polyC -mul_polyC mulrA -[RHS]mul_polyC.
  f_equal.
  rewrite mul_polyC scale_constpoly.
  f_equal.
  by rewrite q_bicoef_compute //.
Qed.

Lemma q_binom_pos_q_binom0 a n :
  (q_binom_pos_poly (- a) n).[0] = q ^+ (n * (n - 1))./2 * a ^+ n.
Proof.
by rewrite -q_binom_posE q_binomx0.
Qed.

Lemma hoDq'_q_binom0 n j a : q_fact n != 0 -> (j <= n)%N ->
  ((Dq' \^ j) (q_binom_pos_poly (- a) n)).[0] =
  (q_bicoef n j * q_fact j) *
   q ^+ ((n - j) * (n - j - 1))./2 * a ^+ (n - j).
Proof.
move=> Hfact Hj.
by rewrite hoDq'_q_binom // hornerZ q_binom_pos_q_binom0 mulrA.
Qed.

Lemma q_binom_x0 n : q_binom_pos_poly 0 n = 'X^n.
Proof.
elim: n => [|n IH] /=.
- by rewrite expr0.
- by rewrite IH mulr0 subr0 exprSr.
Qed.

Theorem Gauss_binomial' a n : (forall n, q_fact n != 0) ->
  q_binom_pos_poly (-a) n =
  \sum_(0 <= i < n.+1)
    (q_bicoef n i * q ^+ ((n - i) * (n - i - 1))./2
                    * a ^+ (n - i)) *: 'X^i.
Proof.
move=> Hfact.
rewrite (q_Taylorp n (q_binom_pos_poly (-a) n) 0) //; last first.
  by rewrite q_binom_size.
under eq_big_nat => i /andP [_ Hi].
  rewrite hoDq'_q_binom0 //.
  rewrite [(q_binom_pos_poly 0 i / (q_fact i)%:P)]mulrC.
  rewrite polyCV.
  rewrite scalerAl scale_constpoly.
  have -> : q_bicoef n i * q_fact i * q ^+ ((n - i) * (n - i - 1))./2 *
            a ^+ (n - i) / q_fact i =
            q_bicoef n i * q ^+ ((n - i) * (n - i - 1))./2 * a ^+ (n - i).
    rewrite -!mulrA; f_equal; f_equal.
    rewrite mulrC -mulrA; f_equal.
    by rewrite denomK.
  rewrite mul_polyC q_binom_x0.
over.
done.
Qed.

Theorem Gauss_binomial a n : (forall n, q_fact n != 0) ->
  q_binom_pos_poly (-a) n =
  \sum_(0 <= i < n.+1)
    (q_bicoef n i * q ^+ (i * (i - 1))./2 * a ^+ i) *: 'X^(n - i).
Proof.
move=> Hfact.
rewrite big_nat_rev //=.
under eq_big_nat => i /andP [_ Hi].
  rewrite add0n subSS subKn // q_bicoefE //.
over.
by rewrite Gauss_binomial'.
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