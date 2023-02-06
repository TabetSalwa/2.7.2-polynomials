Require Import Validity.
Require Import ZArith.
Require Import Nat_utils.

Lemma valid_succ :
  forall (p : poly) (i : nat),
  valid_bool_i p (S i) = true -> valid_bool_i p i = true.
Proof.
  intro p.
  elim p.

  intros.
  unfold valid_bool_i.
  reflexivity.

  intros.
  simpl.
  apply Bool.andb_true_iff.
  split.
  simpl valid_bool_i in H1.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  apply Bool.andb_true_iff in H2.
  destruct H2.
  revert H1.
  elim n.
  intro.
  discriminate H1.
  intros.
  apply leb_trans with (m := i) (n := n0) (p := S n0).
  assumption.
  apply leb_succ with (n := n0).

  apply Bool.andb_true_iff.
  split.
  simpl valid_bool_i in H1.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  apply Bool.andb_true_iff in H2.
  destruct H2.
  assumption.
  apply Bool.andb_true_iff.
  split.
  simpl valid_bool_i in H1.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  apply Bool.andb_true_iff in H2.
  destruct H2.
  apply Bool.andb_true_iff in H3.
  destruct H3.
  assumption.
  simpl valid_bool_i in H1.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  apply Bool.andb_true_iff in H2.
  destruct H2.
  apply Bool.andb_true_iff in H3.
  destruct H3.
  assumption.
Qed.

Lemma valid_leb :
  forall (p : poly) (m n : nat),
  (m <=? n) = true -> valid_bool_i p n = true -> valid_bool_i p m = true.
Proof.
  intros.
  apply Bool.not_false_is_true.
  intro.
  revert H0.
  apply Bool.not_true_iff_false.
  apply rec_init with (P := fun i => valid_bool_i p i = false) (m := m) (n := n).
  intros.
  apply Bool.not_true_is_false.
  intro.
  revert  H0.
  apply Bool.not_false_iff_true.
  apply valid_succ with (p := p) (i := n0).
  assumption.
  assumption.
  assumption.
Qed.

