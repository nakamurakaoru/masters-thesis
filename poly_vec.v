From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum matrix.
From mathcomp Require Import interval rat.
From mathcomp Require Import boolp classical_sets.
From mathcomp Require Import functions set_interval mathcomp_extra.
From mathcomp Require Import reals ereal signed topology normedtype landau.
From mathcomp Require Import sequences.
From mathcomp Require Import all_algebra.

Section poly_vec.
Variables (R : realType) (P : nat -> {poly R}) (n : nat).
Hypothesis degP : forall i, size (P i) = i.+1.

Definition V := {p : {poly R} | size p <= n.+1}.
Fact poly_vect_iso n : Vector.axiom n V.
Definition poly_vectMixin := VectMixin poly_vect_iso.
Canonical poly_vectType := VectType R V poly_vectMixin.