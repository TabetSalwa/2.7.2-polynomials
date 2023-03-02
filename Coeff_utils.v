Require Import Validity.
Require Import ZArith.
Require Import Nat_utils.
Require Import Z_utils.

Lemma valid_leb :
  forall (p : poly) (m n : nat),
  (m <=? n) = true -> valid_bool_i p n = true -> valid_bool_i p m = true.
Proof.
  induction p.

  intros.
  reflexivity.

  intros.
  simpl valid_bool_i in H0.
  apply Bool.andb_true_iff in H0.
  destruct H0.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  apply Bool.andb_true_iff in H2.
  destruct H2.
  simpl valid_bool_i.
  apply Bool.andb_true_iff.
  split.
  apply leb_trans with (n := n0).
  assumption.
  assumption.

  apply Bool.andb_true_iff.
  split.
  assumption.
  apply Bool.andb_true_iff.
  split.
  assumption.
  assumption.
Qed.

Lemma excluded_middle_poly (p q : poly) :
  p = q \/ p <> q.
Proof.
  revert q.
  induction p.
  induction q.
  destruct excluded_middle_z with (z1 := z) (z2 := z0).
  left.
  apply f_equal with (f := Cst).
  assumption.
  right.
  injection.
  assumption.
  right.
  discriminate.
  intro.
  induction q.
  right.
  discriminate.
  destruct IHp1 with (q := q1).
  destruct excluded_middle_nat with (m := n) (n := n0).
  destruct IHp2 with (q := q2).
  left.
  apply f_equal3 with (f := Poly).
  assumption.
  assumption.
  assumption.
  right.
  injection.
  intro.
  exfalso.
  apply H1.
  assumption.
  right.
  injection.
  intros H2 H3.
  exfalso.
  apply H0.
  assumption.
  right.
  injection.
  intros.
  apply H.
  assumption.
Qed.

