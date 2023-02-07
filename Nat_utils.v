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
