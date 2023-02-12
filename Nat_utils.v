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

Lemma eqb_true_iff (m n : nat) :
  (m =? n) = true <-> m = n.
Proof.
  split.
  revert n.
  induction m.
  induction n.
  intro.
  reflexivity.
  intro.
  discriminate H.
  induction n.
  intro.
  discriminate H.
  intro.
  apply f_equal with (f := S).
  apply IHm with (n := n).
  assumption.
  intro.
  rewrite H.
  apply eqb_refl.
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

Lemma ltb_compare_dec (m n : nat) :
  (m <? n) = true \/ (n <? m) = true \/ m = n.
Proof.
  revert n.
  induction m.
  induction n.
  right.
  right.
  reflexivity.
  left.
  reflexivity.
  induction n.
  right.
  left.
  reflexivity.
  destruct IHm with (n := n).
  left.
  assumption.
  destruct H.
  right.
  left.
  assumption.
  right.
  right.
  apply f_equal with (f := S).
  assumption.
Qed.

Lemma nat_compare_ltb (m n : nat) :
  (m <? n) = true <-> Nat.compare m n = Lt.
Proof.
  revert n.
  induction m.
  induction n.
  split ; intro ; discriminate H.
  split ; intro ; reflexivity.
  induction n.
  split ; intro ; discriminate H.
  apply IHm.
Qed.

Lemma nat_compare_gtb (m n : nat) :
  (n <? m) = true <-> Nat.compare m n = Gt.
Proof.
  revert n.
  induction m.
  induction n ; split ; intro ; discriminate H.
  induction n.
  split ; intro ; reflexivity.
  apply IHm.
Qed.

Lemma nat_compare_eq (n : nat) :
  Nat.compare n n = Eq.
Proof.
  induction n.
  reflexivity.
  apply IHn.
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

Lemma ltb_is_neqb2 :
  forall (m n : nat),
  (m <? n) = true ->
  (n =? m) = false.
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
  (n <? m) = false <->
  (m <=? n) = true.
Proof.
  split.
  unfold Nat.ltb.
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


Lemma leb_ltb :
  forall (m n : nat),
  (n <=? m) = false <->
  (m <? n) = true.
Proof.
  split.
  unfold Nat.ltb.
  revert m.
  induction n.
  induction m.
  discriminate.
  discriminate.

  induction m.
  intro.
  simpl.
  reflexivity.
  intro.
  simpl.
  apply IHn with (m := m).
  simpl in H.
  assumption.

  revert m.
  induction n.
  induction m.
  discriminate.
  discriminate.
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

Lemma excluded_middle_nat (m n : nat) :
  m = n \/ m <> n.
Proof.
  revert n.
  induction m.
  induction n.
  left.
  reflexivity.
  right.
  discriminate.
  induction n.
  right.
  discriminate.
  destruct IHm with (n := n).
  left.
  apply f_equal with (f := S).
  assumption.
  right.
  injection.
  assumption.
Qed.

