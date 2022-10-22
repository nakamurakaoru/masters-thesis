From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum matrix.
From mathcomp Require Import interval rat.
From mathcomp.classical Require Import boolp classical_sets.
From mathcomp.classical Require Import functions set_interval mathcomp_extra.
Require Import reals ereal signed topology normedtype landau.
Require Import sequences.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section test.
Variable R : realType.
Variable q : {posnum R}.

Definition qnat (n : nat) := (1 - q%:num ^+ n) / (1 - q%:num).

Lemma cvg_qnat : q%:num < 1 -> qnat --> (1 - q%:num)^-1.
Proof.
move=> q1.
have := @cvg_geometric_series R 1 q%:num.
rewrite ger0_norm// => /(_ q1).
rewrite div1r /qnat/= /series/=.
suff -> : (fun n => \sum_(0 <= k < n) 1 * q%:num ^+ k) =
       (fun n => (1 - q%:num ^+ n) / (1 - q%:num)) by [].
apply/funext => n.
elim: n => [|n].
  by rewrite big_mkord big_ord0 expr0 subrr mul0r.
rewrite big_mkord => ih.
rewrite big_mkord big_ord_recr/=.
rewrite {}ih mul1r.
rewrite -[X in _ + X]mulr1.
rewrite -[X in _ + _ * X](@divrr _ (1 - q%:num)) ?unitfE ?subr_eq0 ?gt_eqF//.
rewrite mulrA.
rewrite -mulrDl.
congr (_ / _).
rewrite mulrDr mulr1.
rewrite addrA.
rewrite subrK.
rewrite exprS.
by rewrite mulrN mulrC.
Qed.

Lemma cvg_qnat2 : q%:num < 1 -> qnat --> (1 - q%:num)^-1.
Proof.
move=> q1.
apply/cvg_distP => _/posnumP[e].
rewrite near_map.
near=> n.
rewrite /qnat.
rewrite -{1}div1r.
rewrite -mulrBl.
rewrite opprB addrCA subrr addr0.
rewrite ger0_norm//; last admit.
rewrite ltr_pdivr_mulr ?subr_gt0//.
???

xxx

see squeeze
see inv_continuous
