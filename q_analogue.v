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

(* 移項 *)
Lemma transposition (a b c : R) : a + b = c -> a = c - b.
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

Definition dq (f : R -> R) x := f (q * x) - f x.
(* dq : (R -> R) -> R -> R であるが, dq : (R => R) -> (R -> R) の方がよいか？ *)

Lemma dq_prod f g x :
  dq (f ** g) x = (f (q * x)) * dq g x + (g x) * dq f x.
Proof.
  rewrite /dq.
  rewrite !GRing.mulrBr.
  rewrite [in g x * f (q * x)] GRing.mulrC.
  rewrite [in g x * f x] GRing.mulrC.
  by rewrite GRing.subrKA.
Qed.

Definition Dq f x := (dq f x) / (dq (fun x => x) x).
(* dq と同様 *)

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

Definition qnat n : R := (q ^ n - 1) / (q - 1).

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

Lemma qderiv_prod f g x :
  x != 0 -> Dq (f ** g) x = f (q * x) * Dq g x + (g x) * Dq f x.
Proof.
  move=> Hx.
  rewrite /Dq dq_prod -GRing_add_div.
    by rewrite !GRing.mulrA.
  by apply denom_is_nonzero.
Qed.

Lemma qderiv_prod' f g x :
  x != 0 ->  Dq (f ** g) x = (f x) * Dq g x + g (q * x) * Dq f x.
Proof.
  move=> Hx.
  by rewrite mulfC qderiv_prod // GRing.addrC.
Qed.

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

Lemma qderiv_quot f g x : x != 0 -> g x != 0 -> g (q * x) != 0 ->
  Dq (f // g) x = (g x * Dq f x - f x * Dq g x) / (g x * g (q * x)).
Proof.
  move=> Hx Hgx Hgqx.
  rewrite -GRing_add_div.
    rewrite red_frac_l // GRing.mulNr.
    apply transposition.
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

Lemma qderiv_quot' f g x : x != 0 -> g x != 0 -> g (q * x) != 0 ->
  Dq (f // g) x =
    (g (q * x) * Dq f x - f (q * x) * Dq g x) / (g x * g (q * x)).
Proof.
  move=> Hx Hgx Hgqx.
  rewrite -GRing_add_div.
    rewrite [g x * g (q * x)] GRing.mulrC.
    rewrite red_frac_l // GRing.mulNr.
    apply transposition.
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

Fixpoint qpoly_nonneg a n x :=
  match n with
  | 0 => 1
  | n.+1 => (qpoly_nonneg a n x) * (x - q ^ n * a)
  end.

(*Lemma prod_qpoly_nonneg x a n :
  qpoly_nonneg x a n.+1 = \prod_(0 <= i < n.+1) (x -  q ^ i * a).
Proof.
  elim: n => [/=|n IH].
  - by rewrite big_nat1 GRing.mul1r.
  - rewrite (@big_cat_nat _ _ _ n.+1) //=.
    by rewrite big_nat1 -IH.
Qed.*)

Theorem qderiv_poly x a n :
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

Lemma qpoly_nonneg_explaw x a m n :
  qpoly_nonneg a (m.+1 + n.+1) x = qpoly_nonneg a m.+1 x * qpoly_nonneg (q ^ m.+1 * a) n.+1 x.
Proof.
  elim: n => [|n IH].
  - by rewrite addSn addn1 /= expr0z !GRing.mul1r.
  - rewrite addnS (lock (m.+1)) [LHS]/= -(lock (m.+1)) IH /=.
    rewrite [q ^ n.+1 * (q ^ m.+1 * a)] GRing.mulrA.
    rewrite [q ^ n.+1 * q ^ m.+1] GRing.mulrC -expfz_n0addr //.
    by rewrite !GRing.mulrA.
Qed.

Definition qpoly_neg a n x := 1 / qpoly_nonneg (q ^ Negz n * a) n x.

Lemma qpoly_0 a x : qpoly_neg a 0 x = qpoly_nonneg a 0 x.
Proof.
  rewrite /qpoly_neg /=.
  rewrite -[RHS] (@GRing.divff _ 1) //.
  by apply GRing.oner_neq0.
Qed.

Definition qpoly a n x :=
  match n with
  | Posz n0 => qpoly_nonneg a n0 x
  | Negz n0 => qpoly_neg a n0 x
  end.

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