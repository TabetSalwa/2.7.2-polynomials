Require Import Nat_utils.
Require Import Validity.
Require Import ZArith. 
Require Import Coeff_utils.
Require Import Coeff.
Require Import Values.

(*         1.3 Arithmetic Operations           *)


(* Question 1.3.a *)

Fixpoint height (p : poly) : nat :=
match p with
| Cst z => 0
| Poly p i q => S (Nat.max (height p) (height q))
end.

Lemma height_l (p q : poly) (i n : nat) :
  height (Poly p i q) <=? S n = true -> height p <=? n = true.
Proof.
  simpl height.
  simpl Nat.leb.
  intro.
  apply leb_trans with (n := Nat.max (height p) (height q)).
  apply leb_max_l.
  assumption.
Qed.

Let height_cst_poly (z : Z) (p q : poly) (i n : nat) :
  height (Cst z) + height (Poly p i q) <=? S n = true -> height (Cst z) + height p <=? n = true.
  intro.
  apply leb_trans with (n := Nat.max (height p) (height q)).
  apply leb_max_l.
  assumption.
Qed.


Let height_poly_cst (p q : poly) (i n : nat) (z : Z) :
  height (Poly p i q) + height (Cst z) <=? S n = true -> height p + height (Cst z) <=? n = true.
  rewrite Nat.add_0_r.
  rewrite Nat.add_0_r.
  intro.
  apply leb_trans with (n := Nat.max (height p) (height q)).
  apply leb_max_l.
  assumption.
Qed.

Let height_poly_poly_eq (p1 p2 q1 q2 : poly) (i j n : nat) :
  height (Poly p1 i p2) + height (Poly q1 j q2) <=? S n = true ->
  height p1 + height q1 <=? n = true /\ height p2 + height q2 <=? n = true.
  intro.
  split.
  apply leb_trans with (n := height p1 + height (Poly q1 j q2)).
  apply leb_plus.
  apply leb_refl with (n := height p1).
  apply leb_trans with (n := Nat.max (height q1) (height q2)).
  apply leb_max_l.
  apply leb_succ.
  apply leb_trans with (m := S (height p1) + height (Poly q1 j q2)) (n := height (Poly p1 i p2) + height (Poly q1 j q2)) (p := S n).
  apply leb_plus_simpl with (c := height (Poly q1 j q2)).
  apply leb_max_l.
  assumption.
  apply leb_trans with (n := height p2 + height (Poly q1 j q2)).
  apply leb_plus.
  apply leb_refl with (n := height p2).
  apply leb_trans with (n := Nat.max (height q1) (height q2)).
  apply leb_max_r.
  apply leb_succ.
  apply leb_trans with (m := S (height p2) + height (Poly q1 j q2)) (n := height (Poly p1 i p2) + height (Poly q1 j q2)) (p := S n).
  apply leb_plus_simpl with (c := height (Poly q1 j q2)).
  apply leb_max_r.
  assumption.
Qed.

Let height_poly_poly_lt (p1 p2 q1 q2 : poly) (i j n : nat) :
  height (Poly p1 i p2) + height (Poly q1 j q2) <=? S n = true ->
  height p1 + height (Poly q1 j q2) <=? n = true.
  intro.
  apply leb_trans with (m := S (height p1) + height (Poly q1 j q2)) (n := height (Poly p1 i p2) + height (Poly q1 j q2)) (p := S n).
  apply leb_plus_simpl with (c := height (Poly q1 j q2)).
  apply leb_max_l.
  assumption.
Qed.

Let height_poly_poly_gt (p1 p2 q1 q2 : poly) (i j n : nat) :
  height (Poly p1 i p2) + height (Poly q1 j q2) <=? S n = true ->
  height (Poly p1 i p2) + height q1 <=? n = true.
  intro.
  apply leb_trans with (m := S (height (Poly p1 i p2) + height q1)) (n := height (Poly p1 i p2) + height (Poly q1 j q2)) (p := S n).
  rewrite Nat.add_comm with (m := height q1) (n := height (Poly p1 i p2)).
  rewrite Nat.add_comm with (m := height (Poly q1 j q2)) (n := height (Poly p1 i p2)).
  apply leb_plus_simpl with (c := height (Poly p1 i p2)).
  apply leb_max_l.
  assumption.
Qed.

(*Fixpoint sum_poly (p q : poly) (n : nat) (H : (height p + height q <=? n) = true) {struct n} : poly :=
  match p,q,n with
  |Cst z1, Cst z2, _ => Cst (z1 + z2)
  |Cst z, Poly q1 j q2, S m => Poly (sum_poly (Cst z) q1 m (height_cst_poly z q1 q2 j m H)) j q2
  |Poly p1 i p2, Cst z, S m => Poly (sum_poly p1 (Cst z) m (height_poly_cst p1 p2 z i m H)) i p2
  |Poly p1 i p2, Poly q1 j q2, S m => 
    match Nat.compare i j with
    | Eq =>
        let H0 := height_poly_poly_eq p1 p2 q1 q2 i j m H in
        Poly (sum_poly p1 q1 m (proj1 H0)) i (sum_poly p2 q2 m (proj2 H0))
    | Lt => Poly (sum_poly p1 (Poly q1 j q2) m (height_poly_poly_lt p1 p2 q1 q2 i j m H)) i p2
    | Gt => Poly (sum_poly (Poly p1 i p2) q1 m (height_poly_poly_gt p1 p2 q1 q2 i j m H)) j q2
    end
  | _ , _ , 0 => Cst 0
end.*)

Fixpoint sum_poly_height (p q : poly) (n : nat) {struct n} : poly :=
  match p,q,n with
  |Cst z1, Cst z2, _ => Cst (z1 + z2)
  |Cst z, Poly q1 j q2, S m => Poly (sum_poly_height (Cst z) q1 m) j q2
  |Poly p1 i p2, Cst z, S m => Poly (sum_poly_height p1 (Cst z) m) i p2
  |Poly p1 i p2, Poly q1 j q2, S m => 
    match Nat.compare i j with
    | Eq => Poly (sum_poly_height p1 q1 m) i (sum_poly_height p2 q2 m)
    | Lt => Poly (sum_poly_height p1 (Poly q1 j q2) m) i p2
    | Gt => Poly (sum_poly_height (Poly p1 i p2) q1 m) j q2
    end
  | _ , _ , 0 => Cst 0
end.

Fixpoint validify (p : poly) :=
match p with
|Cst z => Cst z
|Poly p1 i p2 =>
  let q := validify p2 in
  if is_null q then validify p1 else Poly (validify p1) i q
end.

Definition sum_poly_base (p q : poly) :=
  validify (sum_poly_height p q (height p + height q)).

Lemma height_invariance (p q : poly) (n : nat) :
  (height p + height q <=? n) = true -> sum_poly_height p q n = sum_poly_height p q (height p + height q).
Proof.
  revert n q.
  induction p.
  intros n q.
  revert n.

  induction q.
  intro.
  elim n.
  reflexivity.
  intros.
  reflexivity.

  simpl Nat.add.
  intro m.
  elim m.
  intro.
  discriminate H.
  intros.
  simpl sum_poly_height.
  apply f_equal with (f := fun q => Poly q n q2).
  rewrite IHq1 with (n := n0).
  rewrite IHq1 with (n := Nat.max (height q1) (height q2)).
  reflexivity.
  apply leb_max_l.
  apply leb_trans with (n := Nat.max (height q1) (height q2)).
  apply leb_max_l.
  assumption.

  intros m q.
  revert m.
  induction q.
  simpl Nat.add.
  intro m.
  elim m.
  intro.
  discriminate H.
  intros.
  simpl sum_poly_height.
  apply f_equal with (f := fun q => Poly q n p2).
  rewrite IHp1 with (n := n0).
  rewrite Nat.add_0_r.
  rewrite Nat.add_0_r.
  rewrite IHp1 with (n := Nat.max (height p1) (height p2)).
  rewrite Nat.add_0_r.
  reflexivity.
  rewrite Nat.add_0_r.
  apply leb_max_l.
  apply leb_trans with (n := Nat.max (height p1) (height p2)).
  rewrite Nat.add_0_r.
  apply leb_max_l.
  rewrite Nat.add_0_r in H0.
  assumption.

  intro m.
  elim m.
  intro.
  discriminate H.
  intros.
  simpl sum_poly_height.
  elim (Nat.compare n n0).
  apply f_equal2 with (f := fun p q => Poly p n q).
  rewrite IHp1 with (n := n1).
  rewrite IHp1 with (n := Nat.max (height p1) (height p2) + S (Nat.max (height q1) (height q2))).
  reflexivity.
  apply leb_plus.
  apply leb_max_l.
  apply leb_trans with (n := Nat.max (height q1) (height q2)).
  apply leb_max_l.
  apply leb_succ.
  apply height_poly_poly_eq with (p1 := p1) (p2 := p2) (q1 := q1) (q2 := q2) (i := n) (j := n0) (n := n1).
  assumption.
  rewrite IHp2 with (n := n1).
  rewrite IHp2 with (n := Nat.max (height p1) (height p2) + S (Nat.max (height q1) (height q2))).
  reflexivity.
  apply leb_plus.
  apply leb_max_r.
  apply leb_trans with (n := Nat.max (height q1) (height q2)).
  apply leb_max_r.
  apply leb_succ.
  apply height_poly_poly_eq with (p1 := p1) (p2 := p2) (q1 := q1) (q2 := q2) (i := n) (j := n0) (n := n1).
  assumption.

  apply f_equal with (f := fun p => Poly p n p2).
  rewrite IHp1 with (n := n1).
  rewrite IHp1 with (n := Nat.max (height p1) (height p2) + S (Nat.max (height q1) (height q2))).
  reflexivity.
  apply leb_plus.
  apply leb_max_l.
  apply leb_refl.
  apply leb_trans with (m := S (height p1) + height (Poly q1 n0 q2)) (n := height (Poly p1 n p2) + height (Poly q1 n0 q2)) (p := S n1).
  apply leb_plus_simpl with (c := height (Poly q1 n0 q2)).
  apply leb_max_l.
  assumption.

  apply f_equal with (f := fun p => Poly p n0 q2).
  rewrite IHq1 with (m := n1).
  rewrite IHq1 with (m := Nat.max (height p1) (height p2) + S (Nat.max (height q1) (height q2))).
  reflexivity.
  rewrite <- plus_n_Sm with (n := Nat.max (height p1) (height p2)) (m := Nat.max (height q1) (height q2)).
  simpl height.
  simpl Nat.leb.
  apply leb_plus.
  apply leb_refl.
  apply leb_max_l.
  apply leb_trans with (m := S (height (Poly p1 n p2) + height q1)) (n := height (Poly p1 n p2) + height (Poly q1 n0 q2)) (p := S n1).
  rewrite plus_n_Sm with (n := height (Poly p1 n p2)) (m := height q1).
  apply leb_plus.
  apply leb_refl.
  apply leb_max_l.
  assumption.
Qed.

Fixpoint almost_valid_i (p : poly) (j : nat) : bool :=
match p with
| Cst z => true
| Poly p i q =>
  andb (Nat.leb j i) (andb (almost_valid_i p (S i)) (almost_valid_i q i))
end.

Remark valid_is_almost (p : poly) (i : nat) :
  valid_bool_i p i = true -> almost_valid_i p i = true.
Proof.
  revert i.
  induction p.
  intro.
  reflexivity.
  intros.
  simpl valid_bool_i in H.
  apply Bool.andb_true_iff in H.
  destruct H.
  apply Bool.andb_true_iff in H0.
  destruct H0.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  simpl almost_valid_i.
  apply Bool.andb_true_iff.
  split.
  assumption.
  apply Bool.andb_true_iff.
  split.
  apply IHp1.
  assumption.
  apply IHp2.
  assumption.
Qed.

Lemma almost_valid_leb (p : poly) (m n : nat) :
  (m <=? n) = true -> almost_valid_i p n = true -> almost_valid_i p m = true.
Proof.
  revert m n.
  induction p.
  intros.
  reflexivity.
  intros.
  simpl almost_valid_i in H0.
  apply Bool.andb_true_iff in H0.
  destruct H0.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  simpl almost_valid_i.
  apply Bool.andb_true_iff.
  split.  
  apply leb_trans with (n := n0).
  assumption.
  assumption.
  apply Bool.andb_true_iff.
  split.
  assumption.
  assumption.
Qed.

Lemma sum_almost_valid (p q : poly) (n i : nat) :
  almost_valid_i p i = true -> almost_valid_i q i = true-> almost_valid_i (sum_poly_height p q n) i = true.
Proof.
  revert q n i.
  induction p.
  induction q.
  intros.
  elim n.
  reflexivity.
  intros.
  reflexivity.

  intros.
  elim n0.
  reflexivity.
  intros.
  simpl almost_valid_i in H0.
  apply Bool.andb_true_iff in H0.
  destruct H0.
  apply Bool.andb_true_iff in H2.
  destruct H2.
  simpl sum_poly_height.
  simpl almost_valid_i.
  apply Bool.andb_true_iff.
  split.
  assumption.
  apply Bool.andb_true_iff.
  split.
  apply IHq1.
  reflexivity.
  assumption.
  assumption.

  induction q.
  intros.
  elim n0.
  reflexivity.
  intros.
  simpl almost_valid_i in H.
  apply Bool.andb_true_iff in H.
  destruct H.
  apply Bool.andb_true_iff in H2.
  destruct H2.
  simpl sum_poly_height.
  simpl almost_valid_i.
  apply Bool.andb_true_iff.
  split.
  assumption.
  apply Bool.andb_true_iff.
  split.
  apply IHp1.
  assumption.
  assumption.
  assumption.

  intros.
  elim n1.
  reflexivity.
  intros.
  simpl sum_poly_height.
  simpl almost_valid_i in H.
  apply Bool.andb_true_iff in H.
  destruct H.
  apply Bool.andb_true_iff in H2.
  destruct H2.
  simpl almost_valid_i in H0.
  apply Bool.andb_true_iff in H0.
  destruct H0.
  apply Bool.andb_true_iff in H4.
  destruct H4.

  destruct ltb_compare_dec with (n := n) (m := n0).
  destruct nat_compare_gtb with (m := n) (n := n0).
  rewrite H7.
  simpl almost_valid_i.
  apply Bool.andb_true_iff.
  split.
  assumption.
  apply Bool.andb_true_iff.
  split.
  apply IHq1.
  simpl almost_valid_i.
  apply Bool.andb_true_iff.
  split.
  assumption.
  apply Bool.andb_true_iff.
  split.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.

  destruct H6.
  destruct nat_compare_ltb with (m := n) (n := n0).
  rewrite H7.
  simpl almost_valid_i.
  apply Bool.andb_true_iff.
  split.
  assumption.
  apply Bool.andb_true_iff.
  split.
  apply IHp1.
  assumption.
  simpl almost_valid_i.
  apply Bool.andb_true_iff.
  split.
  assumption.
  apply Bool.andb_true_iff.
  split.
  assumption.
  assumption.
  assumption.
  assumption.

  rewrite H6.
  rewrite Nat_utils.nat_compare_eq with (n := n).
  simpl almost_valid_i.
  apply Bool.andb_true_iff.
  split.
  assumption.
  apply Bool.andb_true_iff.
  split.
  apply IHp1.
  assumption.
  rewrite <- H6.
  assumption.
  apply IHp2.
  assumption.
  rewrite <- H6.
  assumption.
Qed.

Search Z.mul.

Lemma validify_eval (p : poly) (f : nat -> Z) :
  eval_base (validify p) f = eval_base p f.
Proof.
  induction p.
  reflexivity.
  destruct Bool.bool_dec with (b1 := is_null (validify p2)) (b2 := true).
  simpl.
  rewrite e.
  rewrite <- IHp2.
  apply is_null_iff in e.
  rewrite e.
  rewrite Z.mul_0_r.
  rewrite Z.add_0_r.
  apply IHp1.
  apply Bool.not_true_iff_false in n0.
  simpl.
  rewrite n0.
  simpl.
  rewrite IHp1.
  rewrite IHp2.
  reflexivity.
Qed.

Lemma validify_validity (p : poly) (i : nat) :
  almost_valid_i p i = true -> valid_bool_i (validify p) i = true.
Proof.
  revert i.
  induction p.
  intros.
  reflexivity.

  intros.
  simpl almost_valid_i in H.
  apply Bool.andb_true_iff in H.
  destruct H.
  apply Bool.andb_true_iff in H0.
  destruct H0.
  simpl validify.
  destruct Bool.bool_dec with (b1 := is_null (validify p2)) (b2 := true).
  rewrite e.
  apply valid_leb with (n := S n).
  apply leb_trans with (n := n).
  assumption.
  apply leb_succ.
  apply IHp1.
  assumption.
  apply Bool.not_true_iff_false in n0.
  rewrite n0.
  simpl valid_bool_i.
  apply Bool.andb_true_iff.
  split.
  assumption.
  apply Bool.andb_true_iff.
  split.
  apply Bool.negb_true_iff.
  assumption.
  apply Bool.andb_true_iff.
  split.
  apply IHp1.
  assumption.
  apply IHp2.
  assumption.
Qed.

Lemma sum_valid (p q : poly) :
  valid_bool p = true -> valid_bool q = true -> valid_bool (sum_poly_base p q) = true.
Proof.
  intros.
  apply validify_validity.
  apply sum_almost_valid.
  apply valid_is_almost.
  assumption.
  apply valid_is_almost.
  assumption.
Qed.

Definition sum_poly (p q : valid_poly) : valid_poly :=
  {| VP_value := sum_poly_base (VP_value p) (VP_value q) ;
     VP_prop := sum_valid (VP_value p) (VP_value q) (VP_prop p) (VP_prop q) |}.

Lemma eval_sum (p q : valid_poly) (f : nat -> Z) :
  eval (sum_poly p q) f = Z.add (eval p f) (eval q f).
Proof.
  destruct p as [p p'].
  destruct q as [q q'].
  unfold eval.
  simpl VP_value.
  unfold sum_poly_base.
  rewrite validify_eval.
  revert q q'.
  induction p.
  induction q.
  intros.
  reflexivity.
  simpl.
  intro.
  rewrite height_invariance with (n := Nat.max (height q1) (height q2)).
  rewrite IHq1.
  symmetry.
  apply Z.add_assoc.
  unfold valid_bool in q'.
  simpl valid_bool_i in q'.
  apply Bool.andb_true_iff in q'.
  destruct q'.
  apply Bool.andb_true_iff in H0.
  destruct H0.
  apply valid_leb with (n := S n).
  reflexivity.
  assumption.
  apply leb_max_l.

  induction q.
  simpl.
  intro.
  rewrite Nat.add_0_r with (n := Nat.max (height p1) (height p2)).
  rewrite height_invariance with (n := Nat.max (height p1) (height p2)).
  rewrite IHp1.
  simpl.
  rewrite <- Z.add_assoc with (n := eval_base p1 f) (m := z) (p := Z.mul (f n) (eval_base p2 f)).
  rewrite <- Z.add_comm with (m := z) (n := Z.mul (f n) (eval_base p2 f)).
  apply Z.add_assoc with (n := eval_base p1 f) (m := Z.mul (f n) (eval_base p2 f)) (p := z).
  unfold valid_bool in p'.
  simpl valid_bool_i in p'.
  apply Bool.andb_true_iff in p'.
  destruct p'.
  apply Bool.andb_true_iff in H0.
  destruct H0.
  apply valid_leb with (n := S n).
  reflexivity.
  assumption.
  assumption.
  rewrite Nat.add_0_r.
  apply leb_max_l.

  intros.
  destruct ltb_compare_dec with (m := n) (n := n0).
  simpl eval_base.
  destruct nat_compare_ltb with (m := n) (n := n0).
  rewrite H0.
  simpl.
  rewrite height_invariance with (n := Nat.max (height p1) (height p2) + S (Nat.max (height q1) (height q2))).
  rewrite IHp1.
  simpl.
  Lia.lia.
  unfold valid_bool in p'.
  simpl valid_bool_i in p'.
  apply Bool.andb_true_iff in p'.
  destruct p'.
  apply Bool.andb_true_iff in H3.
  destruct H3.
  apply valid_leb with (n := S n).
  reflexivity.
  assumption.
  assumption.
  apply leb_plus_simpl.
  apply leb_max_l.
  assumption.

  destruct H.
  simpl eval_base.
  destruct nat_compare_gtb with (m := n) (n := n0).
  rewrite H0.
  simpl.
  rewrite height_invariance with (n := Nat.max (height p1) (height p2) + S (Nat.max (height q1) (height q2))).
  rewrite IHq1.
  simpl.
  Lia.lia.
  unfold valid_bool in q'.
  simpl valid_bool_i in q'.
  apply Bool.andb_true_iff in q'.
  destruct q'.
  apply Bool.andb_true_iff in H3.
  destruct H3.
  apply valid_leb with (n := S n0).
  reflexivity.
  assumption.
  simpl height.
  rewrite Nat.add_succ_r.
  simpl.
  apply leb_plus.
  apply leb_refl.
  apply leb_max_l.
  assumption.

  rewrite <- H.
  simpl eval_base.
  rewrite Nat_utils.nat_compare_eq with (n := n).
  simpl.
  unfold valid_bool in p'.
  simpl valid_bool_i in p'.
  apply Bool.andb_true_iff in p'.
  destruct p'.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  unfold valid_bool in q'.
  simpl valid_bool_i in q'.
  apply Bool.andb_true_iff in q'.
  destruct q'.
  apply Bool.andb_true_iff in H4.
  destruct H4.
  rewrite height_invariance with (n := Nat.max (height p1) (height p2) + S (Nat.max (height q1) (height q2))).
  rewrite height_invariance with (n := Nat.max (height p1) (height p2) + S (Nat.max (height q1) (height q2))).
  rewrite IHp1.
  rewrite IHp2.
  Lia.lia.
  apply valid_leb with (n := n).
  reflexivity.
  assumption.
  apply valid_leb with (n := n0).
  reflexivity.
  assumption.
  apply valid_leb with (n := S n).
  reflexivity.
  assumption.
  apply valid_leb with (n := S n0).
  reflexivity.
  assumption.
  apply leb_plus.
  apply leb_max_r.
  apply leb_trans with (n := Nat.max (height q1) (height q2)).
  apply leb_max_r.
  apply leb_succ.
  apply leb_plus.
  apply leb_max_l.
  apply leb_trans with (n := Nat.max (height q1) (height q2)).
  apply leb_max_l.
  apply leb_succ.
Qed.

