From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum matrix.
From mathcomp Require Import interval rat.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import functions set_interval mathcomp_extra.
From mathcomp Require Import reals ereal signed topology normedtype landau.
From mathcomp Require Import sequences.
From mathcomp Require Import all_algebra.
Require Import q_tools q_analogue.
From mathcomp Require Import fraction.

Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Import FracField.
Import q_analogue.

Section q_analogue_farc.
Variable (R : realType) (q : R).
Hypothesis Hq : q - 1 != 0.

Local Notation tofrac := (@tofrac [idomainType of {poly R}]).
Local Notation "x %:F" := (tofrac x).
(* Goal (\n_(repr ((tofrac 1) / (tofrac (1 + 'X))))).[0] = 1.
rewrite unlock /repr_of /= /EquivQuot.erepr /=.
rewrite !unlock /=.
Abort. *)

Lemma test1 : ('X ^+ 2)%:F / 'X%:F = 'X%:F.
Proof.
rewrite expr2 tofracM -mulrA divrr ?mulr1 //.
by rewrite unitfE -tofrac0 tofrac_eq polyX_eq0.
Qed.

Lemma sumW {V : zmodType} n (F : nat -> V) :
  \sum_(i < n) F i = \sum_(0 <= i < n) F i.
Proof. by rewrite big_mkord. Qed.

(* Lemma tofrac_div (p p' p'' : {poly R}) : p = p' * p'' -> p %/ p' = p''.
Proof.

Qed. *)

(* Lemma tofrac_div p p' : p%:F / p'%:F = (p %/ p')%:F.
Proof.
Unset Printing Notations.
Locate GRing.inv.
rewrite tofracM.
f_equal.
Admitted. *)

Lemma polyX_div n : (polyX R) ^ n.+1 %/ (polyX R) = (polyX R) ^ n.
Proof.
by rewrite exprSzr mulpK ?polyX_eq0.
Qed.

(* Notation "f ** g" := (fun x => f x * g x) (at level 49).
Notation "f // g" := (fun x => f x / g x) (at level 49).
Notation "a */ f" := (fun x => a * (f x)) (at level 49). *)

Notation "D # p" := (polyderiv R D p) (at level 49).
Notation "D \^ n" := (hoD D n) (at level 49).

Definition scaleq (p : {poly R}):= \poly_(i < size p) (q ^ i * p`_i).

Lemma scaleq_prod p p' : scaleq (p * p') = scaleq p * scaleq p'.
Proof.
Admitted.

Definition dq_f p := scaleq p - p.

Lemma dq_f_prod' p p' : dq_f (p * p') = p * dq_f p' + scaleq p' * dq_f p.
Proof.
rewrite /dq_f scaleq_prod !mulrBr [RHS]addrC addrA.
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

Lemma dq_f_dqE p x : (dq_f p).[x] = (dq R q # p) x.
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
Admitted.

Lemma Dq_fE' p : Dq_f p = dq_f p %/ ((q - 1) *: 'X).
Proof. by rewrite /Dq_f dq_fXE. Qed.

Lemma Dq_f_prod' p p' : Dq_f (p * p') = p * Dq_f p' + scaleq p' * Dq_f p.
Proof.
rewrite /Dq_f !divp_mulA ?Dq_f_ok //.
by rewrite -divpD dq_f_prod'.
Qed.

(* Lemma horner_div (p p' : {poly R}) x : (p %/ p').[x] = p.[x] / p'.[x].
Proof.
Admitted. *)

(* Lemma Dq_f_DqE p x : (Dq_f p).[x] = (Dq R q # p) x.
Proof.
rewrite Dq_fE'.
rewrite /dq_f horner_div dq_fE hornerZ hornerX.
by rewrite /Dq /dq [(q - 1) * x]mulrBl mul1r.
Qed. *)

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

Lemma divpsum n P (d : {poly R}) :
  (\sum_(0 <= i < n) P i) %/ d = \sum_(0 <= i < n) (P i %/ d).
Proof.
elim: n => [|n IH].
- by rewrite !big_nil div0p.
- by rewrite !(@big_cat_nat _ _ _ n 0 n.+1) //= !big_nat1 divpD IH.
Qed.

Lemma Dq_f_Dq'E p : Dq_f p = Dq' R q p.
Proof.
case Hsize : (size p == 0%N).
- move: Hsize.
  rewrite size_poly_eq0 => /eqP ->.
  rewrite Dq_f_const.
  rewrite /Dq' poly_def.
  rewrite (sumW _ (fun i => (q_nat R q i.+1 * 0%:P`_i.+1) *: 'X^i)).
  by rewrite size_poly0 big_nil.
- have Hsize' : (0 < size p)%N.
    rewrite ltn_neqAle.
    apply /andP; split => //.
    move: Hsize.
    by rewrite eq_sym => ->.
  rewrite Dq_fE' /dq_f /scaleq /Dq' -{3}(coefK p) !poly_def.
  rewrite (sumW _ (fun i => (q ^ i * p`_i) *: 'X^i)).
  rewrite (sumW _ (fun i => p`_i *: 'X^i)).
  rewrite (sumW _ (fun i => (q_nat R q i.+1 * p`_i.+1) *: 'X^i)).
  rewrite sum_sub.
  rewrite divpsum.
  under eq_bigr => i _.
    rewrite -scalerBl -{2}(mul1r p`_i) -mulrBl scale_div //.
    have -> : (q ^ i - 1) * p`_i / (q - 1) = (q ^ i - 1) / (q - 1) * p`_i.
      by rewrite -mulrA [p`_i / (q - 1)]mulrC mulrA.
    rewrite -/(q_nat R q i).
  over.
  move=> /=.
  rewrite (@big_cat_nat _ _ _ 1) //=.
  rewrite big_nat1 q_nat_0 mul0r scale0r add0r.
  have -> : (1 = 0 + 1)%N by [].
  rewrite big_addn.
  under eq_bigr do rewrite addn1 polyX_div.
  rewrite (@big_cat_nat _ _ _ (size p - 1) 0 (size p)) //=; last first.
    by rewrite subn1 leq_pred.
  have {4}-> : size p = ((size p) - 1).+1.
    by rewrite subn1 prednK.
  rewrite big_nat1.
  have -> : p`_(size p - 1).+1 = 0.
    rewrite subn1 prednK //.
    by apply /(leq_sizeP _ (size p)) => //=.
  by rewrite mulr0 scale0r addr0.
Qed.

(* Lemma Dq'_DqE p x : (Dq' R q p).[x] = (Dq R q # p) x.
Proof.
by rewrite -Dq_fE -Dq_f_DqE.
Qed. *)

Lemma hoDq_f_Dq'E n p :
  (Dq_f \^ n) p = ((Dq' R q \^ n) p).
Proof.
  elim: n => [|n IH] //=.
  by rewrite Dq_f_Dq'E IH.
Qed.

Lemma Dq'_prod' p p' :
   Dq' R q (p * p') = p * Dq' R q p' + scaleq p' * Dq' R q p.
Proof. by rewrite -!Dq_f_Dq'E Dq_f_prod'. Qed.

(* Lemma Dq_f_pow n : Dq_f ('X ^ n.+1) = (q_nat R q n.+1) *: 'X ^ n.
Proof.
elim: n => [|n IH] //=.
- rewrite q_nat1 // scale1r.
  rewrite /Dq_f /dq_f poly_def size_polyX.
  rewrite (sumW _ (fun i => (q ^ i * 'X`_i) *: 'X^i)).
  rewrite (@big_cat_nat _ _ _ 1) //= !big_nat1.
  rewrite !coefX /= mulr0 scale0r add0r expr1z mulr1.
  rewrite -{2 4}(scale1r 'X) -scalerBl.
  rewrite scale_div ?divff ?scale1r //.
  have -> : 'X^1 = (polyX R) ^0.+1 by [].
  by rewrite polyX_div.
- rewrite /Dq_f /dq_f.
Admitted. *)
