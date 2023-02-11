Require Import ZArith.

Lemma eqb_refl :
  forall (n : nat), (n =? n) = true.
Proof.
  induction n.
  simpl.
  reflexivity.
  simpl.
  assumption.
Qed.

Lemma eqb_symm :
  forall (m n : nat),
  (n =? m) = (m =? n).
Proof.
  intro m.
  induction m.
  induction n.
  simpl.
  reflexivity.
  reflexivity.
  induction n.
  reflexivity.
  apply IHm with (n := n).
Qed.

Lemma leb_refl :
  forall (n : nat), (n <=? n) = true.
Proof.
  induction n.
  reflexivity.
  assumption.
Qed.

Lemma ltb_or_leb :
  forall (m n : nat),
  (n <? m) = true \/ (m <=? n) = true.
Proof.
  induction m.
  induction n.
  right.
  reflexivity.
  right.
  reflexivity.
  induction n.
  left.
  reflexivity.
  destruct IHm with (n := n).
  left.
  assumption.
  right.
  assumption.
Qed.


Lemma leb_trans :
  forall (m n p: nat),
    (m <=? n) = true -> (n <=? p) = true -> (m <=? p) = true.
Proof.
  induction m.
  simpl.
  reflexivity.

  destruct n.
  simpl.
  intros.
  discriminate H.

  destruct p. 
  simpl.
  intros.
  discriminate H0.
  simpl.
  apply IHm.
Qed.

Lemma leb_antisymm :
  forall (m n : nat),
  (m <=? n) = true ->
  (n <=? m) = true ->
  m = n.
Proof.
  induction m.
  induction n.
  intros.
  reflexivity.
  intro.
  simpl.
  intro.
  discriminate H0.

  induction n.
  simpl.
  intro.
  discriminate H.

  simpl.
  intros.
  apply f_equal with (f := S).
  apply IHm with (n := n).
  assumption.
  assumption.
Qed.

Lemma leb_succ :
  forall (n : nat),
    (n <=? (S n)) = true.
Proof.
  induction n.
  simpl.
  reflexivity.
  simpl.
  assumption.
Qed.

Lemma ltb_is_neqb :
  forall (m n : nat),
  (m <? n) = true ->
  (m =? n) = false.
Proof.
  induction m.
  induction n.
  unfold Nat.ltb.
  simpl.
  intro.
  discriminate H.
  intro.
  simpl.
  reflexivity.

  induction n.
  intro.
  simpl.
  reflexivity.
  unfold Nat.ltb.
  simpl.
  intro.
  apply IHm with (n := n).
  assumption.
Qed.

Lemma ltb_antisymm :
  forall (m n : nat),
  (m <? n) = true ->
  (n <? m) = false.
Proof.
  induction m.
  induction n.
  intro.
  unfold Nat.ltb.
  simpl.
  reflexivity.
  intro.
  unfold Nat.ltb.
  simpl.
  reflexivity.

  induction n.
  unfold Nat.ltb.
  simpl.
  intro.
  discriminate H.
  unfold Nat.ltb.
  simpl.
  intro.
  apply IHm with (n := n).
  assumption.
Qed.

Lemma ltb_leb :
  forall (m n : nat),
  (n <? m) = false ->
  (m <=? n) = true.
Proof.
  unfold Nat.ltb.
  intros m n.
  revert m.
  induction n.
  induction m.
  intro.
  simpl.
  reflexivity.
  simpl.
  intro.
  discriminate H.

  induction m.
  intro.
  simpl.
  reflexivity.
  intro.
  simpl.
  apply IHn with (m := m).
  simpl in H.
  assumption.
Qed.

Lemma leb_max_l (m n : nat) :
  m <=? Nat.max m n = true.
Proof.
  revert n.
  induction m.
  induction n.
  reflexivity.
  reflexivity.
  induction n.
  unfold Nat.max.
  apply leb_refl.
  apply IHm with (n := n).
Qed.

Lemma leb_max_r (m n : nat) :
  n <=? Nat.max m n = true.
Proof.
  revert m.
  induction n.
  induction m.
  reflexivity.
  reflexivity.
  induction m.
  apply leb_refl.
  apply IHn with (m := m).
Qed.

Lemma leb_plus_simpl (m n c : nat) :
  (m <=? n) = true -> (m + c <=? n + c) = true.
Proof.
  induction c.
  intro.
  rewrite Nat.add_0_r.
  rewrite Nat.add_0_r.
  assumption.
  rewrite Nat.add_comm with (m := S c) (n := m).
  rewrite Nat.add_comm with (m := S c) (n := n).
  intro.
  simpl Nat.add.
  simpl Nat.leb.
  rewrite Nat.add_comm with (m := m) (n := c).
  rewrite Nat.add_comm with (m := n) (n := c).
  apply IHc.
  assumption.
Qed.

Lemma leb_plus (m1 m2 n1 n2 : nat) :
  (m1 <=? m2) = true -> (n1 <=? n2) = true -> m1 + n1 <=? m2 + n2 = true.
Proof.
  intros.
  apply leb_trans with (n := m1 + n2).
  rewrite Nat.add_comm with (m := n1) (n := m1).
  rewrite Nat.add_comm with (m := n2) (n := m1).
  apply leb_plus_simpl.
  assumption.
  apply leb_plus_simpl.
  assumption.
Qed.

Lemma rec_init :
  forall (P : nat -> Prop),
  (forall (n : nat), P n -> P (S n)) ->
  forall (m n : nat), (m <=? n) = true -> P m -> P n.
Proof.
  intros P H m n.
  revert P H n.

  induction m.
  intros.
  induction n.
  assumption.
  apply H.
  apply IHn.
  assumption.

  induction n.
  intro.
  discriminate H0.

  intros.
  apply IHm with (P := fun i => P (S i)).
  intro.
  apply H with (n := S n0).
  simpl in H0.
  assumption.
  assumption.
Qed.

Lemma z_integrity (m n : Z) :
  (Z.mul m n = Z.zero) <-> (m = Z.zero) \/ (n = Z.zero).
Proof.
  split.
  revert n.
  induction m.
  intros.
  left.
  reflexivity.
  intros.
  right.
  induction n.
  reflexivity.
  simpl Z.mul in H.
  discriminate H.
  simpl Z.mul in H.
  discriminate H.

  intros.
  induction n.
  right.
  reflexivity.
  simpl Z.mul in H.
  discriminate H.
  simpl Z.mul in H.
  discriminate H.

  intro.
  destruct H.
  rewrite H.
  simpl Z.mul.
  reflexivity.
  rewrite H.
  induction m.
  reflexivity.
  reflexivity.
  reflexivity.
Qed.

Import Z.

Lemma add_simpl (m n p : Z) :
  Z.add m p = Z.add n p -> m = n.
Proof.
  intro.
  rewrite <- add_0_r with (n := m).
  rewrite <- add_0_r with (n := n).
  rewrite <- add_opp_diag_r with (n := p).
  rewrite add_assoc with (n := m) (m := p) (p := Z.opp p).
  rewrite add_assoc with (n := n) (m := p) (p := Z.opp p).
  rewrite H.
  reflexivity.
Qed.
