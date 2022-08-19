From mathcomp Require Import all_ssreflect all_algebra.
(*Import Numtheory.*)
(* algebra の中の　ssrnum *)

Axiom funext : forall A B (f g : A -> B), f =1 g -> f = g.

Section q_analogue.
Local Open Scope ring_scope.
Variable (R : rcfType) (q : R).
Hypothesis Hq : q - 1 != 0.

Notation "f +/ g" := (fun x => f x + g x) (at level 49).
Notation "f ** g" := (fun x => f x * g x) (at level 49).
Notation "f // g" := (fun x => f x / g x) (at level 49).
Notation "a */ f" := (fun x => a * (f x)) (at level 49).

(* tools *)
(* 関数の積の交換 *)
Lemma mulfC (f g : R -> R) : f ** g = g ** f.
Proof.
  apply funext => x.
  by rewrite GRing.mulrC.
Qed.

Lemma NegzK m n : Negz (m + n) + n = Negz m.
Proof.
  rewrite !NegzE.
  rewrite GRing.addrC.
  rewrite -addn1.
  rewrite (_ : Posz (m + n + 1)%N = Posz m + n + 1) //.
  rewrite -[Posz m + n + 1] GRing.addrA.
  rewrite [Posz m + (Posz n + 1)] GRing.addrC.
  rewrite -[Posz n + 1 + m] GRing.addrA.
  rewrite -{1}(GRing.add0r (Posz n)).
  rewrite GRing.addrKA.
  rewrite -addn1.
  rewrite GRing.sub0r.
  by rewrite addnC.
Qed.

Lemma mulnon0 (a b : R) : a * b != 0 -> a != 0.
Proof.
  move/eqP.
  case_eq (a == 0) => //.
  move/eqP ->.
  by rewrite GRing.mul0r.
Qed.

Lemma expnon0 (x : R) (n : nat) : x != 0 -> x ^ n != 0.
Proof.
  move=> Hx.
  elim: n => [|n IH].
  - by rewrite expr0z GRing.oner_neq0.
  - by rewrite exprSz GRing.mulf_neq0.
Qed.

(* add cancel *)
Lemma addrK (a : R) : a - a = 0.
Proof. by rewrite -{1}(GRing.add0r a) GRing.addrK. Qed.

Lemma Negz_rK n c : Negz n.+1 + c - c = Negz n.+1.
Proof. by rewrite GRing.addrK. Qed.

(* 移項 *)
Lemma rtransposition (a b c : R) : a + b = c -> a = c - b.
Proof.
  move=> <-.
  by rewrite GRing.addrK.
Qed.

Theorem itransposition (l m n : int) : l + m = n -> l = n - m.
Proof.
  move=> <-.
  by rewrite GRing.addrK.
Qed.

(* 両辺にかける *)
Lemma same_prod {a b} (c : R) : c != 0 -> a * c = b * c -> a = b.
Proof.
  move=> Hc.
  rewrite -{2}(GRing.mulr1 a).
  rewrite -{2}(GRing.mulr1 b).
  rewrite -(@GRing.divff _ c) //.
  by rewrite !GRing.mulrA => ->.
Qed.

(* 約分 *)
Lemma red_frac_r (x y z : R) : z != 0 -> x * z / (y * z) = x / y.
Proof.
  move=> Hz.
  rewrite -GRing.mulf_div.
  by rewrite GRing.divff // GRing.mulr1.
Qed.

Lemma red_frac_l (x y z : R) : z != 0 -> z * x / (z * y) = x / y.
Proof.
  move=> Hz.
  rewrite [z * x] GRing.mulrC.
  rewrite [z * y] GRing.mulrC.
  by rewrite red_frac_r.
Qed.

(* 分母共通の和 *)
Lemma GRing_add_div (x y z : R) : z != 0 -> x / z + y / z = (x + y) / z.
Proof.
  move=> nz0.
  rewrite GRing.addf_div //.
  rewrite -GRing.mulrDl.
  by rewrite red_frac_r.
Qed.

(* 頻出分母が0でない *)
Lemma denom_is_nonzero x : x != 0 -> q * x - x != 0.
Proof.
  move=> Hx.
  rewrite -{2}(GRing.mul1r x).
  rewrite -GRing.mulrBl.
  by apply GRing.mulf_neq0.
Qed.

(* main *)

(* q-differential *)
Definition dq (f : R -> R) x := f (q * x) - f x.
(* dq : (R -> R) -> R -> R であるが, dq : (R => R) -> (R -> R) の方がよいか？ *)

(* q-differential product rule *)
Lemma dq_prod f g x :
  dq (f ** g) x = (f (q * x)) * dq g x + (g x) * dq f x.
Proof.
  rewrite /dq.
  rewrite !GRing.mulrBr.
  rewrite [in g x * f (q * x)] GRing.mulrC.
  rewrite [in g x * f x] GRing.mulrC.
  by rewrite GRing.subrKA.
Qed.

(* q-derivative *)
Definition Dq f x := (dq f x) / (dq (fun x => x) x).
(* dq と同様 *)

(* q-derivative for const is 0 *)
Lemma Dq_const x c : Dq (fun x => c) x = 0.
Proof.
  rewrite /Dq /dq.
  by rewrite addrK GRing.mul0r.
Qed.


(* q-derivative is linear *)
Lemma Dq_is_linear f g a b x :
  x != 0 -> Dq ((a */ f) +/ (b */ g)) x = a * (Dq f x) + b * (Dq g x).
Proof.
  move=> Hx.
  rewrite /Dq /dq.
  rewrite !GRing.mulrA.
  rewrite GRing_add_div.
    rewrite !GRing.mulrBr.
    rewrite GRing.opprD.
    rewrite !GRing.addrA.
    rewrite [a * f (q * x) + b * g (q * x) - a * f x] GRing.addrC.
    rewrite [(a * f (q * x) + b * g (q * x))] GRing.addrC.
    rewrite GRing.addrA.
    rewrite [- (a * f x) + b * g (q * x) + a * f (q * x)] GRing.addrC.
    by rewrite GRing.addrA.
  by apply denom_is_nonzero.
Qed.

(* q-analogue of natural number *)
Definition qnat n : R := (q ^ n - 1) / (q - 1).

(* qnat 0 is 0 *)
Lemma qnat_0 : qnat 0 = 0.
Proof. by rewrite /qnat expr0z addrK GRing.mul0r. Qed.

(*Lemma lim_qnat n :
  forall e : R, e > 0 -> exists d, `|q - 1| < d -> `|n - (qnat n)| < e.
Proof.

Qed.*)

(* q-derivative of x ^ n *)
Lemma qderiv_of_pow n x :
  x != 0 -> Dq (fun x => x ^ n) x = qnat n * x ^ (n - 1).
Proof.
  move=> Hx.
  rewrite /Dq /dq /qnat.
  rewrite -{4}(GRing.mul1r x).
  rewrite -GRing.mulrBl.
  rewrite expfzMl.
    rewrite -GRing_add_div.
    rewrite [in x ^ n](_ : n = (n -1) +1) //.
      rewrite expfzDr //.
      rewrite expr1z.
      rewrite GRing.mulrA.
      rewrite -GRing.mulNr.
      rewrite !red_frac_r //.
      rewrite GRing_add_div //.
      rewrite -{2}[x ^ (n - 1)]GRing.mul1r.
      rewrite -GRing.mulrBl.
      rewrite GRing.mulrC GRing.mulrA.
      by rewrite [in (q - 1)^-1 * (q ^ n - 1)] GRing.mulrC.
    by rewrite GRing.subrK.
  by apply GRing.mulf_neq0.
Qed.

(* q-derivative product rule *)
Lemma qderiv_prod f g x :
  x != 0 -> Dq (f ** g) x = f (q * x) * Dq g x + (g x) * Dq f x.
Proof.
  move=> Hx.
  rewrite /Dq dq_prod -GRing_add_div.
    by rewrite !GRing.mulrA.
  by apply denom_is_nonzero.
Qed.

(* q-derivative product rule' *)
Lemma qderiv_prod' f g x :
  x != 0 ->  Dq (f ** g) x = (f x) * Dq g x + g (q * x) * Dq f x.
Proof.
  move=> Hx.
  by rewrite mulfC qderiv_prod // GRing.addrC.
Qed.

(* reduce fraction in q-derivative *)
Lemma qderiv_divff f g x : g x != 0 -> g (q * x) != 0 ->
  Dq (g ** (f // g)) x = Dq f x.
Proof.
  move=> Hgx Hgqx.
  rewrite /Dq /dq.
  rewrite [f (q * x) / g (q * x)] GRing.mulrC.
  rewrite [f x / g x] GRing.mulrC.
  rewrite !GRing.mulrA.
  rewrite !GRing.divff //.
  by rewrite !GRing.mul1r.
Qed.

(* q-derivative quotient rule *)
Lemma qderiv_quot f g x : x != 0 -> g x != 0 -> g (q * x) != 0 ->
  Dq (f // g) x = (g x * Dq f x - f x * Dq g x) / (g x * g (q * x)).
Proof.
  move=> Hx Hgx Hgqx.
  rewrite -GRing_add_div.
    rewrite red_frac_l // GRing.mulNr.
    apply rtransposition.
    apply (same_prod (g (q * x))) => //.
    rewrite GRing.mulrDl.
    rewrite -[f x * Dq g x / (g x * g (q * x)) * g (q * x)] GRing.mulrA.
    rewrite [(g x * g (q * x))^-1 * g (q * x)] GRing.mulrC.
    rewrite GRing.mulrA.
    rewrite red_frac_r //.
    rewrite -[Dq f x / g (q * x) * g (q * x)] GRing.mulrA.
    rewrite [(g (q * x))^-1 * g (q * x)] GRing.mulrC.
    rewrite GRing.divff // GRing.mulr1.
    rewrite GRing.mulrC.
    rewrite -[f x * Dq g x / g x] GRing.mulrA.
    rewrite [Dq g x / g x] GRing.mulrC.
    rewrite [f x * ((g x)^-1 * Dq g x)] GRing.mulrA.
    rewrite -qderiv_prod //.
    by apply qderiv_divff.
  by apply GRing.mulf_neq0.
Qed.

(* q-derivative quotient rule' *)
Lemma qderiv_quot' f g x : x != 0 -> g x != 0 -> g (q * x) != 0 ->
  Dq (f // g) x =
    (g (q * x) * Dq f x - f (q * x) * Dq g x) / (g x * g (q * x)).
Proof.
  move=> Hx Hgx Hgqx.
  rewrite -GRing_add_div.
    rewrite [g x * g (q * x)] GRing.mulrC.
    rewrite red_frac_l // GRing.mulNr.
    apply rtransposition.
    apply (same_prod (g x)) => //.
    rewrite GRing.mulrDl.
    rewrite [f (q * x) * Dq g x / (g (q * x) * g x) * g x] GRing.mulrC.
    rewrite [g (q * x) * g x] GRing.mulrC.
    rewrite GRing.mulrA.
    rewrite red_frac_l //.
    rewrite -[Dq f x / g x * g x] GRing.mulrA.
    rewrite [(g x)^-1 * g x] GRing.mulrC.
    rewrite GRing.divff // GRing.mulr1.
    rewrite GRing.mulrC.
    rewrite -[f (q * x) * Dq g x / g (q * x)] GRing.mulrA.
    rewrite [Dq g x / g (q * x)] GRing.mulrC.
    rewrite [f (q * x) * ((g (q * x))^-1 * Dq g x)] GRing.mulrA.
    rewrite -qderiv_prod' //.
    by apply qderiv_divff.
  by apply GRing.mulf_neq0.
Qed.

(* q-analogue of polynomial for nat *)
Fixpoint qpoly_nonneg a n x :=
  match n with
  | 0 => 1
  | n.+1 => (qpoly_nonneg a n x) * (x - q ^ n * a)
  end.

Lemma qpoly_nonneg_head a n x:
   qpoly_nonneg a n.+1 x = (x - a) * qpoly_nonneg (q * a) n x.
Proof.
  elim: n => [|n IH] /=.
  - by rewrite expr0z !GRing.mul1r GRing.mulr1.
  - by rewrite !GRing.mulrA -IH exprSzr.
Qed.

(*Lemma prod_qpoly_nonneg a n x :
  qpoly_nonneg a n.+1 x = \prod_(0 <= i < n.+1) (x -  q ^ i * a).
Proof.
  elim: n => [/=|n IH].
  - by rewrite big_nat1 GRing.mul1r.
  - rewrite (@big_cat_nat _ _ _ n.+1) //=.
    by rewrite big_nat1 -IH.
Qed.*)

(* q-derivative of q-polynomial for nat *)
Theorem qderiv_qpoly_nonneg a n x :
  x != 0 -> Dq (qpoly_nonneg a n.+1) x = qnat n.+1 * qpoly_nonneg a n x.
Proof.
  move=> Hx.
  elim: n => [|n IH].
  - rewrite /Dq /dq /qpoly_nonneg /qnat.
    rewrite !GRing.mul1r GRing.mulr1 expr1z.
    rewrite GRing.opprB.
    rewrite GRing.subrKA.
    rewrite !GRing.divff //.
    rewrite -{2}(GRing.mul1r x).
    rewrite -(GRing.mulrBl x).
    by apply GRing.mulf_neq0.
  - rewrite (_ : Dq (qpoly_nonneg a n.+2) x =
                 Dq ((qpoly_nonneg a n.+1) **
                 (fun x => (x - q ^ (n.+1) * a))) x) //.
    rewrite qderiv_prod' //.
    rewrite [Dq (+%R^~ (- (q ^ n.+1 * a))) x] /Dq /dq.
    rewrite GRing.opprB GRing.subrKA GRing.divff //.
      rewrite GRing.mulr1 exprSz.
      rewrite -[q * q ^ n * a] GRing.mulrA.
      rewrite -(GRing.mulrBr q).
      rewrite IH.
      rewrite -[q * (x - q ^ n * a) * (qnat n.+1 * qpoly_nonneg a n x)] GRing.mulrA.
      rewrite [(x - q ^ n * a) * (qnat n.+1 * qpoly_nonneg a n x)] GRing.mulrC.
      rewrite -[qnat n.+1 * qpoly_nonneg a n x * (x - q ^ n * a)] GRing.mulrA.
      rewrite (_ : qpoly_nonneg a n x * (x - q ^ n * a) = qpoly_nonneg a n.+1 x) //.
      rewrite GRing.mulrA.
      rewrite -{1}(GRing.mul1r (qpoly_nonneg a n.+1 x)).
      rewrite -GRing.mulrDl.
      rewrite GRing.addrC.
      rewrite -(@GRing.divff _ (q - 1)) //.
      rewrite [qnat n.+1] /qnat.
      rewrite [q * ((q ^ n.+1 - 1) / (q - 1))] GRing.mulrA.
      rewrite (GRing_add_div _ _ (q -1)) //.
      by rewrite GRing.mulrBr -exprSz GRing.mulr1 GRing.subrKA.
    by apply denom_is_nonzero.
Qed.

(* q-polynomial exponential law for nat *)
Lemma qpoly_nonneg_explaw x a m n :
  qpoly_nonneg a (m + n) x =
    qpoly_nonneg a m x * qpoly_nonneg (q ^ m * a) n x.
Proof.
  elim: n.
  - by rewrite addn0 /= GRing.mulr1.
  - elim => [_|n _ IH].
    + by rewrite addnS /= addn0 expr0z !GRing.mul1r.
    + rewrite addnS [LHS]/= IH /=.
      rewrite !GRing.mulrA.
      by rewrite -[q ^ n.+1 * q ^ m] expfz_n0addr // addnC.
Qed.

(* q-polynomial for neg *)
Definition qpoly_neg a n x := 1 / qpoly_nonneg (q ^ ((Negz n) + 1) * a) n x.

(* q-poly_nat 0 = q-poly_neg 0 *)
Lemma qpoly_0 a x : qpoly_neg a 0 x = qpoly_nonneg a 0 x.
Proof.
  rewrite /qpoly_neg /=.
  rewrite -[RHS] (@GRing.divff _ 1) //.
  by apply GRing.oner_neq0.
Qed.

Theorem qpoly_neg_inv a n x :
  qpoly_nonneg (q ^ (Negz n + 1) * a) n x != 0 ->
  qpoly_neg a n x * qpoly_nonneg (q ^ (Negz n + 1) * a) n x = 1.
Proof.
  move=> H.
  rewrite /qpoly_neg.
  rewrite GRing.mulrC.
  rewrite GRing.mulrA.
  rewrite GRing.mulr1.
  by rewrite GRing.divff.
Qed.

(* q-analogue polynomial for int *)
Definition qpoly a n x :=
  match n with
  | Posz n0 => qpoly_nonneg a n0 x
  | Negz n0 => qpoly_neg a n0.+1 x
  end.

Lemma Dq_qpoly_int_to_neg a n x :
  Dq (qpoly a (Negz n)) x = Dq (qpoly_neg a (n + 1)) x.
Proof. by rewrite /Dq /dq /= addn1. Qed.

(*Lemma qpoly_ex a (n : nat) x : qpoly a (- 1) x = 1 / (x - q ^ (- 1) * a) .
Proof.
  move=> /=.
  rewrite /qpoly_neg /=.
  rewrite expr0z !GRing.mul1r.
  rewrite (_ : Negz 1 + 1 = - 1) //.
Qed.*)

Lemma qpoly_exp_0 a m n x : m = 0 \/ n = 0 ->
  qpoly a (m + n) x = qpoly a m x * qpoly (q ^ m * a) n x.
Proof.
  move=> [->|->].
  - by rewrite GRing.add0r expr0z /= !GRing.mul1r.
  - by rewrite GRing.addr0 /= GRing.mulr1.
Qed.

Theorem qpoly_exp_law a m n x :
  qpoly a (m + n) x = qpoly a m x * qpoly (q ^ m * a) n x.
Proof.
  case: m => m.
  - case: n => n.
    + by apply qpoly_nonneg_explaw.
    + case_eq (Posz m + Negz n) => l Hmnl /=.
      - rewrite /qpoly_neg.
        rewrite (_ : Posz m = Posz m + Negz n + n).
        rewrite -[LHS]GRing.divr1.
        rewrite -(red_frac_r _ _ (qpoly_nonneg (q ^ (Posz m + Negz n) * a) n x)).
      - 
  -
Admitted.

Lemma qpoly_exp_neg_pos a m n x : m < 0 /\ n > 0 ->
  qpoly a (m + n) x = qpoly a m x * qpoly (q ^ m * a) n x.
Proof.
  move=> [Hm Hn].
  case_eq (m + n) => l Hl /=.
  -
  -
Admitted.

(* q-derivative of q-polynomial for 0 *)
Lemma qderiv_qpoly_0 a x :
  Dq (qpoly a 0) x = qnat 0 * qpoly a (- 1) x.
Proof.
  by rewrite Dq_const qnat_0 GRing.mul0r.
Qed.

Lemma qpoly_qx a m n x : q != 0 ->
  qpoly_nonneg (q ^ m * a) n (q * x) =
    q ^ n * qpoly_nonneg (q ^ (m - 1) * a) n x.
Proof.
  move=> Hq0.
  elim: n => [|n IH] /=.
  - by rewrite expr0z GRing.mul1r.
  - rewrite IH.
    rewrite exprSzr.
    rewrite -[RHS]GRing.mulrA.
    rewrite [q * (qpoly_nonneg (q ^ (m - 1) * a) n x *
              (x - q ^ n * (q ^ (m - 1) * a)))] GRing.mulrA.
    rewrite [q * qpoly_nonneg (q ^ (m - 1) * a) n x] GRing.mulrC.
    rewrite -[qpoly_nonneg (q ^ (m - 1) * a) n x * q *
               (x - q ^ n * (q ^ (m - 1) * a))] GRing.mulrA.
    rewrite [q * (x - q ^ n * (q ^ (m - 1) * a))] GRing.mulrBr.
    rewrite [q * (q ^ n * (q ^ (m - 1) * a))] GRing.mulrA.
    rewrite [q * q ^ n] GRing.mulrC.
    rewrite -[q ^ n * q * (q ^ (m - 1) * a)] GRing.mulrA.
    rewrite (_ : q * (q ^ (m - 1) * a) = q ^ m * a).
      by rewrite [RHS] GRing.mulrA.
    rewrite GRing.mulrA.
    rewrite -{1}(expr1z q).
    by rewrite -expfzDr // GRing.addrC GRing.subrK.
Qed.

(* q-derivative of q-polynomial for neg *)
Theorem qderiv_qpoly_neg a n x : q != 0 -> x != 0 ->
  (x - q ^ (Negz n) * a) != 0 ->
  qpoly_nonneg (q ^ (Negz n + 1) * a) n x != 0 ->
  Dq (qpoly_neg a n) x = qnat (Negz n + 1) * qpoly_neg a (n.+1) x.
Proof.
  move=> Hq0 Hx Hqn Hqpoly.
  destruct n.
  - by rewrite /Dq /dq /qpoly_neg /= addrK qnat_0 !GRing.mul0r.
  - rewrite qderiv_quot //.
      rewrite Dq_const GRing.mulr0 GRing.mul1r GRing.sub0r.
      rewrite qderiv_qpoly_nonneg //.
      rewrite qpoly_qx //.
      rewrite -GRing.mulNr.
      rewrite [qpoly_nonneg (q ^ (Negz n.+1 + 1) * a) n.+1 x *
                (q ^ n.+1 * qpoly_nonneg (q ^ (Negz n.+1 + 1 - 1) *
                  a) n.+1 x)] GRing.mulrC.
      rewrite -GRing.mulf_div.
      have -> : qpoly_nonneg (q ^ (Negz n.+1 + 1) * a) n x /
                    qpoly_nonneg (q ^ (Negz n.+1 + 1) * a) n.+1 x =
                      1 / (x - q ^ (- 1) * a).
        rewrite -(GRing.mulr1
                     (qpoly_nonneg (q ^ (Negz n.+1 + 1) * a) n x)) /=.
        rewrite red_frac_l.
          rewrite NegzE.
          rewrite GRing.mulrA.
          rewrite -expfzDr //.
          rewrite GRing.addrA.
          rewrite -addn2.
          rewrite (_ : Posz (n + 2)%N = Posz n + 2) //.
          rewrite -{1}(GRing.add0r (Posz n)).
          by rewrite GRing.addrKA.
        rewrite /= in Hqpoly.
        by apply mulnon0 in Hqpoly.
      rewrite GRing.mulf_div.
      rewrite -[q ^ n.+1 *
                 qpoly_nonneg (q ^ (Negz n.+1 + 1 - 1) * a) n.+1 x *
                   (x - q ^ (-1) * a)]GRing.mulrA.
      have -> : qpoly_nonneg (q ^ (Negz n.+1 + 1 - 1) * a) n.+1 x *
                (x - q ^ (-1) * a) =
                qpoly_nonneg (q ^ (Negz (n.+1)) * a) n.+2 x => /=.
        have -> : Negz n.+1 + 1 - 1 = Negz n.+1.
          by rewrite GRing.addrK.
        have -> : q ^ n.+1 * (q ^ Negz n.+1 * a) = q ^ (-1) * a => //.
        rewrite GRing.mulrA.
        rewrite -expfzDr //.
        rewrite NegzE.
        have -> : Posz n.+1 - Posz n.+2 = - 1 => //.
        rewrite -addn1.
        rewrite -[(n + 1).+1]addn1.
        rewrite (_ : Posz (n + 1)%N = Posz n + 1) //.
        rewrite (_ : Posz (n + 1 + 1)%N = Posz n + 1 + 1) //.
        rewrite -(GRing.add0r (Posz n + 1)).
        by rewrite GRing.addrKA.
      rewrite /qpoly_neg /=.
      rewrite (_ : Negz n.+2 + 1 = Negz n.+1) //.
      rewrite -GRing.mulf_div.
      congr (_ * _).
      rewrite NegzE GRing.mulrC.
      rewrite /qnat.
      rewrite -GRing.mulNr GRing.mulrA.
      congr (_ / _).
      rewrite GRing.opprB GRing.mulrBr GRing.mulr1 GRing.mulrC GRing.divff.
        rewrite invr_expz.
        rewrite (_ : - Posz n.+2 + 1 = - Posz n.+1) //.
        rewrite -addn1.
        rewrite (_ : Posz (n.+1 + 1)%N = Posz n.+1 + 1) //.
        rewrite GRing.addrC.
        rewrite [Posz n.+1 + 1]GRing.addrC.
        rewrite -{1}(GRing.add0r 1).
        by rewrite GRing.addrKA GRing.sub0r.
      by rewrite expnon0 //.
    rewrite qpoly_qx //.
    rewrite GRing.mulf_neq0 //.
      by rewrite expnon0.
    rewrite qpoly_nonneg_head.
    rewrite GRing.mulf_neq0 //.
    rewrite (_ : Negz n.+1 + 1 - 1 = Negz n.+1) //.
      by rewrite GRing.addrK.
    move: Hqpoly => /=.
    move/mulnon0.
    rewrite GRing.addrK.
    rewrite GRing.mulrA.
    rewrite -{2}(expr1z q).
    by rewrite -expfzDr.
Qed.

Theorem qderiv_qpoly a n x : q != 0 -> x != 0 ->
  x - q ^ (n - 1) * a != 0 ->
  qpoly (q ^ n * a) (- n) x != 0 ->
  Dq (qpoly a n) x = qnat n * qpoly a (n - 1) x.
Proof.
  move=> Hq0 Hx Hxqa Hqpoly.
  case: n Hxqa Hqpoly => [|/=] n Hxqa Hqpoly.
  - destruct n.
    + by rewrite qderiv_qpoly_0.
    + rewrite qderiv_qpoly_nonneg //.
      rewrite (_ : Posz n.+1 - 1 = n) //.
      rewrite -addn1.
      rewrite (_ : Posz (n + 1)%N = Posz n + 1) //.
      by rewrite GRing.addrK.
  - rewrite Dq_qpoly_int_to_neg.
    rewrite qderiv_qpoly_neg //.
        rewrite NegzK.
        rewrite (_ : (n + 1).+1 = (n + 0).+2) //.
        by rewrite addn0 addn1.
      rewrite (_ : Negz (n + 1) = Negz n - 1) //.
      apply itransposition.
      by rewrite NegzK.
    by rewrite NegzK addn1.
Qed.

End q_analogue.

Section q_chain_rule.
Local Open Scope ring_scope.
Variable (R : rcfType).
Notation "f o/ g" := (fun x => f (g x)) (at level 49).

Lemma qchain q u f a b x : dq R q u x != 0 -> u = (fun x => a * x ^ b) ->
  Dq R q (f o/ u) x = (Dq R (q^b) f (u x)) * (Dq R q u x).
Proof.
  move=> Hqu Hu.
  rewrite Hu /Dq /dq.
  rewrite GRing.mulf_div.
  rewrite [(q ^ b * (a * x ^ b) - a * x ^ b) * (q * x - x)] GRing.mulrC.
  rewrite expfzMl.
  rewrite !GRing.mulrA.
  rewrite [a * q ^ b] GRing.mulrC.
  rewrite red_frac_r //.
  move: Hqu.
  rewrite /dq Hu.
  rewrite expfzMl GRing.mulrA.
  by rewrite GRing.mulrC.
Qed.
End q_chain_rule.