Require Import ZArith.
Require Import Nat_utils.

Lemma add_simpl (m n p : Z) :
  Z.add m p = Z.add n p -> m = n.
Proof.
  intro.
  rewrite <- Z.add_0_r with (n := m).
  rewrite <- Z.add_0_r with (n := n).
  rewrite <- Z.add_opp_diag_r with (n := p).
  rewrite Z.add_assoc with (n := m) (m := p) (p := Z.opp p).
  rewrite Z.add_assoc with (n := n) (m := p) (p := Z.opp p).
  rewrite H.
  reflexivity.
Qed.

Lemma excluded_middle_pos (p q : positive) :
  p = q \/ p <> q.
Proof.
  revert q.
  induction p.
  induction q.
  destruct IHp with (q := q).
  left.
  apply f_equal with (f := xI).
  assumption.
  right.
  injection.
  assumption.
  right.
  discriminate.
  right.
  discriminate.
  induction q.
  right.
  discriminate.
  destruct IHp with (q := q).
  left.
  apply f_equal with (f := xO).
  assumption.
  right.
  injection.
  assumption.
  right.
  discriminate.
  induction q.
  right.
  discriminate.
  right.
  discriminate.
  left.
  reflexivity.
Qed.


Lemma excluded_middle_z (z1 z2 : Z) :
  z1 = z2 \/ z1 <> z2.
Proof.
  revert z2.
  induction z1.
  induction z2.
  left.
  reflexivity.
  right.
  discriminate.
  right.
  discriminate.
  induction z2.
  right.
  discriminate.
  destruct excluded_middle_pos with (p := p) (q := p0).
  left.
  apply f_equal with (f := Z.pos).
  assumption.
  right.
  injection.
  assumption.
  right.
  discriminate.
  induction z2.
  right.
  discriminate.
  right.
  discriminate.
  destruct excluded_middle_pos with (p := p) (q := p0).
  left.
  apply f_equal with (f := Z.neg).
  assumption.
  right.
  injection.
  assumption.
Qed.

Lemma affine_not_constant (a b c : Z) :
  a <> Z.zero -> exists (x : Z), x <> Z.zero /\ (b + a * x)%Z <> c.
Proof.
  intro.
  destruct excluded_middle_z with (z1 := (b + a)%Z) (z2 := c).
  exists (2)%Z.
  split.
  discriminate.
  rewrite Z.two_succ.
  rewrite Z.mul_succ_r.
  rewrite Z.mul_1_r.
  rewrite Z.add_assoc.
  rewrite H0.
  intro.
  apply f_equal with (f := fun z => Z.sub z c) in H1.
  revert H1.
  rewrite Z.add_simpl_l.
  rewrite Z.sub_diag.
  assumption.
  exists Z.one.
  split.
  discriminate.
  rewrite Z.mul_1_r.
  assumption.
Qed.

Import Z.

Lemma z_lt_irrefl (z1 z2 : Z) :
  (z1 < z2)%Z -> z1 <> z2.
Proof.
  intro.
  intro.
  revert H.
  rewrite H0.
  apply Z.lt_irrefl.
Qed.

Lemma z_add_pos (z1 z2 : Z) :
  (0 < z1)%Z -> (0 < z2)%Z -> (0 < z1 + z2)%Z.
Proof.
  induction z1.
  intro.
  apply Z.lt_irrefl in H.
  contradiction.
  intro.
  induction z2.
  intro.
  apply Z.lt_irrefl in H0.
  contradiction.
  intro.
  apply Pos2Z.is_pos.
  intro.
  apply Z.lt_asymm in H0.
  exfalso.
  apply H0.
  apply Pos2Z.neg_is_neg.
  induction z2.
  intros.
  apply Z.lt_irrefl in H0.
  contradiction.
  intros.
  apply Z.lt_asymm in H.
  exfalso.
  apply H.
  apply Pos2Z.neg_is_neg.
  intro.
  apply Z.lt_asymm in H.
  exfalso.
  apply H.
  apply Pos2Z.neg_is_neg.
Qed.

Lemma z_mul_pos (z1 z2 : Z) :
  (0 < z1)%Z -> (0 < z2)%Z -> (0 < z1 * z2)%Z.
Proof.
  induction z1.
  intro.
  apply Z.lt_irrefl in H.
  contradiction.
  intro.
  induction z2.
  intro.
  apply Z.lt_irrefl in H0.
  contradiction.
  intro.
  apply Pos2Z.is_pos.
  intro.
  apply Z.lt_asymm in H0.
  exfalso.
  apply H0.
  apply Pos2Z.neg_is_neg.
  induction z2.
  intros.
  apply Z.lt_irrefl in H0.
  contradiction.
  intros.
  apply Z.lt_asymm in H.
  exfalso.
  apply H.
  apply Pos2Z.neg_is_neg.
  intros.
  apply Pos2Z.is_pos.
Qed.

Lemma z_mul_le_0 (z1 z2 : Z) :
  (0 <= z1)%Z -> (0 <= z2)%Z -> (0 <= z1 * z2)%Z.
Proof.
  induction z1.
  intros.
  rewrite Z.mul_0_l.
  apply Z.le_refl.
  intro.
  induction z2.
  intro.
  rewrite Z.mul_0_r.
  apply Z.le_refl.
  intro.
  apply Z.lt_le_incl.
  apply Pos2Z.is_pos.
  intro.
  apply Zle_not_lt in H0.
  exfalso.
  apply H0.
  apply Pos2Z.neg_is_neg.
  induction z2.
  intros.
  rewrite Z.mul_0_r.
  apply Z.le_refl.
  intros.
  apply Zle_not_lt in H.
  exfalso.
  apply H.
  apply Pos2Z.neg_is_neg.
  intros.
  apply Pos2Z.is_nonneg.
Qed.

Lemma z_pos_ge_1 (z : Z) :
  (0 < z)%Z -> (1 <= z)%Z.
Proof.
  elim z.
  intro.
  exfalso.
  apply Z.lt_irrefl with (x := 0%Z).
  assumption.
  intros.
  apply Pos.le_1_l.
  intros.
  apply Z.lt_asymm in H.
  exfalso.
  apply H.
  apply Pos2Z.neg_is_neg.
Qed.

Lemma z_pos_pos_mul (z1 z2 : Z) :
  (0 < z1)%Z -> (0 < z2)%Z -> (z1 <= z1 * z2)%Z.
Proof.
  intros.
  rewrite <- Z.add_simpl_r with (n := (z1 * z2)%Z) (m := z1).
  rewrite <- Z.add_opp_r.
  rewrite <- Z.add_assoc.
  rewrite <- Z.add_comm with (m := z1) (n := (-z1)%Z).
  rewrite Z.add_assoc.
  rewrite <- Z.mul_1_r with (n := (-z1)%Z).
  rewrite <- Zopp_mult_distr_l with (n := z1) (m := 1%Z).
  rewrite Zopp_mult_distr_r with (n := z1) (m := 1%Z).
  rewrite <- Z.mul_add_distr_l.
  rewrite Z.add_opp_r.
  apply Zplus_le_reg_r with (p := (-z1)%Z).
  rewrite <- Z.add_assoc.
  rewrite Z.add_opp_diag_r with (n := z1).
  rewrite Z.add_0_r.
  apply z_mul_le_0.
  apply Z.lt_le_incl.
  assumption.
  apply Zplus_le_reg_r with (p := 1%Z).
  rewrite Z.add_0_l.
  rewrite <- Z.add_opp_r.
  rewrite <- Z.add_assoc.
  rewrite Z.add_opp_diag_l.
  rewrite Z.add_0_r.
  apply z_pos_ge_1.
  assumption.
Qed.

Lemma pos_plus_neg (z : Z) (p : positive) :
  (z * pos p + z * neg p)%Z = 0%Z.
Proof.
  rewrite <- Z.mul_add_distr_l.
  simpl.
  rewrite pos_sub_diag.
  apply Z.mul_0_r.
Qed.

Lemma z_abs_lt (z1 z2 z3 : Z) :
  (Z.abs z1 < z2)%Z -> z3 <> 0%Z -> (z1 + z2 * z3)%Z <> 0%Z.
Proof.
  elim z1.
  intros.
  intro.
  apply z_integrity in H1.
  destruct H1.
  rewrite H1 in H.
  apply Z.lt_irrefl with (x := 0%Z).
  assumption.
  apply H0.
  assumption.

  elim z3.
  intros.
  exfalso.
  apply H0.
  reflexivity.

  intros.
  intro.
  symmetry in H1.
  revert H1.
  apply z_lt_irrefl with (z1 := 0%Z) (z2 := (pos p0 + z2 * pos p)%Z).
  apply z_add_pos.
  apply Pos2Z.is_pos.
  apply z_mul_pos.
  apply Z.lt_trans with (m := Z.pos p0).
  apply Pos2Z.is_pos.
  assumption.
  apply Pos2Z.is_pos.

  intros.
  apply z_lt_irrefl with (z2 := 0%Z) (z1 := (pos p0 + z2 * neg p)%Z).
  rewrite <- pos_plus_neg with (z := z2) (p := p).
  apply Zplus_lt_compat_r with (n := Z.pos p0) (m := (z2 * pos p)%Z) (p := (z2 * neg p)%Z).
  apply Z.lt_le_trans with (m := z2).
  assumption.
  apply z_pos_pos_mul.
  apply Z.lt_trans with (m := Z.pos p0).
  apply Pos2Z.is_pos.
  assumption.
  apply Pos2Z.is_pos.

  elim z3.
  intros.
  exfalso.
  apply H0.
  reflexivity.

  intros.
  intro.
  symmetry in H1.
  revert H1.
  apply z_lt_irrefl with (z1 := 0%Z) (z2 := (neg p0 + z2 * pos p)%Z).
  rewrite <- pos_plus_neg with (z := z2) (p := p).
  rewrite add_comm.
  apply Zplus_lt_compat_r with (m := Z.neg p0) (n := (z2 * neg p)%Z) (p := (z2 * pos p)%Z).
  rewrite <- Pos2Z.opp_pos.
  rewrite <- Pos2Z.opp_pos.
  rewrite <- Zopp_mult_distr_r with (n := z2) (m := Z.pos p).
  apply Z.opp_lt_mono with (m := (z2 * pos p)%Z) (n := Z.pos p0).
  apply Z.lt_le_trans with (m := z2).
  assumption.
  apply z_pos_pos_mul.
  apply Z.lt_trans with (m := Z.pos p0).
  apply Pos2Z.is_pos.
  assumption.
  apply Pos2Z.is_pos.

  intros.
  apply z_lt_irrefl with (z1 := (neg p0 + z2 * neg p)%Z) (z2 := 0%Z).
  rewrite <- Pos2Z.opp_pos.
  rewrite <- Pos2Z.opp_pos.
  rewrite <- Zopp_mult_distr_r with (n := z2) (m := Z.pos p).
  rewrite <- Z.opp_add_distr.
  apply Z.opp_lt_mono with (m := (pos p0 + z2 * pos p)%Z) (n := 0%Z).
  apply z_add_pos.
  apply Pos2Z.is_pos.
  apply z_mul_pos.
  apply Z.lt_trans with (m := Z.pos p0).
  apply Pos2Z.is_pos.
  assumption.
  apply Pos2Z.is_pos.
Qed.
