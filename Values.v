Require Import Nat_utils.
Require Import Validity.
Require Import ZArith. 
Require Import Z_utils.
Require Import Coeff_utils.
Require Import Coeff.
Import Z.

(* Question 1.2.c *)

Fixpoint eval_base (p : poly) (f : nat -> Z) : Z := 
match p with
| Cst z => z
| Poly p1 i p2 => eval_base p1 f + (f i) * (eval_base p2 f)
end.

Definition eval (p : valid_poly) (f : nat -> Z) : Z :=
  eval_base (VP_value p) f.

(* Question 1.2.d *)

Lemma invariance_i (p : poly) (i : nat) (f g : nat -> Z) :
  valid_bool_i p i = true ->
  (forall (j : nat), (i <=? j) = true -> f j = g j) ->
  eval_base p f = eval_base p g.
Proof.
  revert i.
  induction p.
  intros.
  unfold eval_base.
  reflexivity.
  intros.
  simpl eval_base.
  apply Bool.andb_true_iff in H.
  destruct H.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  apply Bool.andb_true_iff in H2.
  destruct H2.
  rewrite IHp1 with (i := i).
  rewrite IHp2 with (i := i).
  rewrite H0 with (j := n).
  reflexivity.
  assumption.
  apply valid_leb with (p := p2) (m := i) (n := n).
  assumption.
  assumption.
  assumption.
  apply valid_leb with (p := p1) (m := i) (n := S n).
  apply leb_trans with (n := n).
  assumption.
  apply leb_succ.
  assumption.
  assumption.
Qed.

Definition zeros : nat -> Z :=
  fun n => Z.zero.

Lemma eval_zero (p : poly) :
  eval_base p zeros = get_coeff_base p One.
Proof.
  induction p.
  unfold get_coeff_base.
  unfold eval_base.
  reflexivity.

  simpl eval_base.
  simpl get_coeff_base.
  Lia.lia.
Qed.

Locate "&&".
Open Scope bool_scope.
Check (true && false) % bool.

Lemma non_constant_poly (p : poly) (i : nat) (z : Z) :
  valid_bool_i p i = true ->
  p <> Cst z ->
  exists (f : nat -> Z) (n0 : Z),
  forall (n : Z), (n0 <= n)%Z ->
  eval_base p (fun (j : nat) => if j =? i then n else f j) <> z.
Proof.
  revert i z.
  induction p.
  intros.
  exists zeros.
  exists Z.zero.
  intros.
  intro.
  apply H0.
  apply f_equal with (f := Cst).
  assumption.

  intros.
  simpl valid_bool_i in H.
  apply Bool.andb_true_iff in H.
  destruct H.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  apply Bool.andb_true_iff in H2.
  destruct H2.

  destruct ltb_compare_dec with (m := n) (n := i).
  exfalso.
  revert H4.
  apply Bool.not_true_iff_false.
  apply ltb_leb.
  assumption.
  destruct H4.
  destruct IHp2 with (i := n) (z := 0%Z).
  assumption.
  apply Bool.negb_true_iff in H1.
  apply Bool.not_true_iff_false in H1.
  intro.
  apply H1.
  apply is_null_iff.
  assumption.
  destruct H5.
  exists (fun j => if j=? n then (max x0 (succ (abs (eval_base p1 x - z)))%Z) else x j).
  exists 0%Z.
  intros.
  simpl eval_base.
  rewrite <- invariance_i with (p := p1) (i := S n) (f := x) (g := fun  (j : nat) => if (j =? i)%nat then n0 else if (j =? n)%nat then max x0 (succ (abs (eval_base p1 x - z))) else x j).
  rewrite ltb_is_neqb2 with (m := i) (n := n).
  rewrite Nat.eqb_refl with (x := n).
  rewrite <- invariance_i with (p := p2) (i := n) (f := fun (j : nat) => if (j =? n)%nat then max x0 (succ (abs (eval_base p1 x - z))) else x j) (g := fun (j : nat) => if (j =? i)%nat then n0 else if (j =? n)%nat then max x0 (succ (abs (eval_base p1 x - z))) else x j).
  intro.
  apply f_equal with (f := fun (x : Z) => Z.sub x z) in H7.
  revert H7.
  rewrite Z.sub_diag.
  rewrite <- Z.add_opp_r.
  rewrite <- Z.add_assoc.
  rewrite Z.add_comm with (m := (-z)%Z).
  rewrite Z.add_assoc.
  rewrite Z.add_opp_r.
  apply z_abs_lt.
  apply Z.lt_le_trans with (m := (succ (abs (eval_base p1 x - z)))%Z).
  apply Z.lt_succ_diag_r.
  apply Z.le_max_r.
  apply H5 with (n := (max x0 (succ (abs (eval_base p1 x - z))))%Z).
  apply Z.le_max_l.
  assumption.
  intros.
  rewrite ltb_is_neqb2 with (m := i) (n := j).
  reflexivity.
  apply leb_trans with (n := n).
  assumption.
  assumption.
  assumption.
  assumption.
  intros.
  rewrite ltb_is_neqb2 with (m := i) (n := j).
  rewrite ltb_is_neqb2 with (m := n) (n := j).
  reflexivity.
  assumption.
  apply leb_trans with (n := n).
  assumption.
  apply leb_trans with (n := S n).
  apply leb_succ.
  assumption.

  rewrite <- H4.
  destruct IHp2 with (i := n) (z := 0%Z).
  assumption.
  apply Bool.negb_true_iff in H1.
  apply Bool.not_true_iff_false in H1.
  intro.
  apply H1.
  apply is_null_iff.
  assumption.
  destruct H5.
  exists x.
  exists (max x0 (succ (abs (eval_base p1 x - z)))%Z).
  intros.
  simpl eval_base.
  rewrite Nat.eqb_refl with (x := n).
  rewrite <- invariance_i with (p := p1) (i := S n) (f := x) (g := fun  (j : nat) => if (j =? n)%nat then n0 else x j).
  intro.
  apply f_equal with (f := fun (x : Z) => Z.sub x z) in H7.
  revert H7.
  rewrite Z.sub_diag.
  rewrite <- Z.add_opp_r.
  rewrite <- Z.add_assoc.
  rewrite Z.add_comm with (m := (-z)%Z).
  rewrite Z.add_assoc.
  rewrite Z.add_opp_r.
  apply z_abs_lt.
  apply Z.lt_le_trans with (m := (succ (abs (eval_base p1 x - z)))%Z).
  apply Z.lt_succ_diag_r.
  apply Z.le_trans with (m := (max x0 (succ (abs (eval_base p1 x - z))))%Z).
  apply Z.le_max_r.
  assumption.
  apply H5 with (n := n0).
  apply Z.le_trans with (m := (max x0 (succ (abs (eval_base p1 x - z))))%Z).
  apply Z.le_max_l.
  assumption.
  assumption.
  intros.
  rewrite ltb_is_neqb2 with (m := n) (n := j).
  reflexivity.
  assumption.
Qed.


Lemma diff_poly (p q : poly) (i : nat) :
  valid_bool_i p i = true -> valid_bool_i q i = true -> p <> q ->
  exists (f : nat -> Z) (n0 : Z), forall (n : Z), (n0 <= n)%Z ->
  eval_base p (fun (j : nat) => if j =? i then n else f j) <> eval_base q (fun (j : nat) => if j =? i then n else f j).
Proof.
  revert i q.
  induction p.
  induction q.
  intros.
  exists zeros.
  exists 0%Z.
  intros.
  intro.
  apply H1.
  apply f_equal with (f := Cst).
  assumption.

  intros.
  simpl eval_base.
  destruct non_constant_poly with (p := Poly q1 n q2) (i := i) (z := z).
  assumption.
  intro.
  apply H1.
  symmetry.
  assumption.
  exists x.
  destruct H2.
  exists x0.
  intros.
  intro.
  symmetry in H4.
  revert H4.
  apply H2 with (n := n0).
  assumption.

  induction q.
  intros.
  simpl eval_base.
  apply non_constant_poly with (p := Poly p1 n p2) (i := i) (z := z).
  assumption.
  assumption.

  intros.
  destruct ltb_compare_dec with (m := n) (n := n0).
  simpl valid_bool_i in H.
  apply Bool.andb_true_iff in H.
  destruct H.
  apply Bool.andb_true_iff in H3.
  destruct H3.
  apply Bool.andb_true_iff in H4.
  destruct H4.
  destruct non_constant_poly with (p := p2) (i := n) (z := 0%Z).
  assumption.
  apply Bool.negb_true_iff in H3.
  apply Bool.not_true_iff_false in H3.
  intro.
  apply H3.
  apply is_null_iff.
  assumption.
  destruct H6.
  exists (fun j => if j =? n then (max x0 (succ (abs (eval_base p1 x - eval_base (Poly q1 n0 q2) x))))%Z else x j).
  exists (max x0 (succ (abs (eval_base p1 x - eval_base (Poly q1 n0 q2) x))))%Z.
  intros.
  rewrite <- invariance_i with (p := Poly q1 n0 q2) (i := n0) (f := x) (g := fun (j : nat) =>
   if j =? i then n1 else if j =? n then (max x0 (succ (abs (eval_base p1 x - eval_base (Poly q1 n0 q2) x))))%Z else x j).
  simpl eval_base.
  rewrite <- invariance_i with (p := p1) (i := S n) (f := x) (g := fun (j : nat) =>
   if j =? i then n1 else if j =? n then (max x0 (succ (abs (eval_base p1 x - (eval_base q1 x + x n0 * eval_base q2 x)))))%Z else x j).
  intro.
  apply f_equal with (f := fun y => (y - (eval_base q1 x + x n0 * eval_base q2 x))%Z) in H8.
  revert H8.
  rewrite Z.sub_diag.
  rewrite <- Z.add_opp_r.
  rewrite <- Z.add_assoc.
  rewrite Z.add_comm with (m := (-(eval_base q1 x + x n0 * eval_base q2 x))%Z).
  rewrite Z.add_assoc.
  rewrite Z.add_opp_r.
  apply z_abs_lt.
  apply Z.lt_le_trans with (m := (max x0 (succ (abs (eval_base p1 x - eval_base (Poly q1 n0 q2) x))))%Z).
  apply Z.lt_le_trans with (m := (succ (abs (eval_base p1 x - eval_base (Poly q1 n0 q2) x)))%Z).
  apply Z.lt_succ_diag_r.
  apply Z.le_max_r.
  elim (n =? i).
  assumption.
  rewrite Nat.eqb_refl with (x := n).
  apply Z.le_refl.
  destruct ltb_compare_dec with (m := n) (n := i).
  exfalso.
  revert H8.
  apply Bool.not_true_iff_false.
  apply ltb_leb.
  assumption.
  destruct H8.
  rewrite <- invariance_i with (p := p2) (i := n) (f := fun (j : nat) => if j =? n then (max x0 (succ (abs (eval_base p1 x - (eval_base q1 x + x n0 * eval_base q2 x)))))%Z else x j).
  apply H6 with (n := (max x0 (succ (abs (eval_base p1 x - (eval_base q1 x + x n0 * eval_base q2 x)))))%Z).
  apply Z.le_max_l.
  assumption.
  intros.
  rewrite ltb_is_neqb2 with (m := i) (n := j).
  reflexivity.
  apply leb_trans with (n := n).
  assumption.
  assumption.
  rewrite <- H8.
  rewrite <- invariance_i with (p := p2) (i := n) (f := fun (j : nat) => if j =? n then n1 else x j).
  apply H6 with (n := n1).
  apply Z.le_trans with (m := (max x0 (succ (abs (eval_base p1 x - eval_base (Poly q1 n0 q2) x))))%Z).
  apply Z.le_max_l.
  assumption.
  assumption.
  intros.
  elim (j =? n).
  reflexivity.
  reflexivity.
  assumption.
  intros.
  rewrite ltb_is_neqb2 with (m := i) (n := j).
  rewrite ltb_is_neqb2 with (m := n) (n := j).
  reflexivity.
  assumption.
  apply leb_trans with (n := S n).
  assumption.
  assumption.
  simpl valid_bool_i in H0.
  apply Bool.andb_true_iff in H0.
  destruct H0.
  simpl valid_bool_i.
  apply Bool.andb_true_iff.
  split.
  apply Nat_utils.leb_refl.
  assumption.
  intros.
  rewrite ltb_is_neqb2 with (m := i) (n := j).
  rewrite ltb_is_neqb2 with (m := n) (n := j).
  reflexivity.
  apply leb_trans with (n := n0).
  assumption.
  assumption.
  apply leb_trans with (n := n0).
  apply leb_trans with (n := S n).
  assumption.
  assumption.
  assumption.

  destruct H2.
  simpl valid_bool_i in H0.
  apply Bool.andb_true_iff in H0.
  destruct H0.
  apply Bool.andb_true_iff in H3.
  destruct H3.
  apply Bool.andb_true_iff in H4.
  destruct H4.
  destruct non_constant_poly with (p := q2) (i := n0) (z := 0%Z).
  assumption.
  apply Bool.negb_true_iff in H3.
  apply Bool.not_true_iff_false in H3.
  intro.
  apply H3.
  apply is_null_iff.
  assumption.
  destruct H6.
  exists (fun j => if j =? n0 then (max x0 (succ (abs (eval_base q1 x - eval_base (Poly p1 n p2) x))))%Z else x j).
  exists (max x0 (succ (abs (eval_base q1 x - eval_base (Poly p1 n p2) x))))%Z.
  intros.
  rewrite <- invariance_i with (p := Poly p1 n p2) (i := n) (f := x) (g := fun (j : nat) =>
   if j =? i then n1 else if j =? n0 then (max x0 (succ (abs (eval_base q1 x - eval_base (Poly p1 n p2) x))))%Z else x j).
  simpl eval_base.
  rewrite <- invariance_i with (p := q1) (i := S n0) (f := x) (g := fun (j : nat) =>
   if j =? i then n1 else if j =? n0 then (max x0 (succ (abs (eval_base q1 x - (eval_base p1 x + x n * eval_base p2 x)))))%Z else x j).
  intro.
  apply f_equal with (f := fun y => (y - (eval_base p1 x + x n * eval_base p2 x))%Z) in H8.
  symmetry in H8.
  revert H8.
  rewrite Z.sub_diag.
  rewrite <- Z.add_opp_r.
  rewrite <- Z.add_assoc.
  rewrite Z.add_comm with (m := (-(eval_base p1 x + x n * eval_base p2 x))%Z).
  rewrite Z.add_assoc.
  rewrite Z.add_opp_r.
  apply z_abs_lt.
  apply Z.lt_le_trans with (m := (max x0 (succ (abs (eval_base q1 x - eval_base (Poly p1 n p2) x))))%Z).
  apply Z.lt_le_trans with (m := (succ (abs (eval_base q1 x - eval_base (Poly p1 n p2) x)))%Z).
  apply Z.lt_succ_diag_r.
  apply Z.le_max_r.
  elim (n0 =? i).
  assumption.
  rewrite Nat.eqb_refl with (x := n0).
  apply Z.le_refl.
  destruct ltb_compare_dec with (m := n0) (n := i).
  exfalso.
  revert H8.
  apply Bool.not_true_iff_false.
  apply ltb_leb.
  assumption.
  destruct H8.
  rewrite <- invariance_i with (p := q2) (i := n0) (f := fun (j : nat) => if j =? n0 then (max x0 (succ (abs (eval_base q1 x - (eval_base p1 x + x n * eval_base p2 x)))))%Z else x j).
  apply H6 with (n := (max x0 (succ (abs (eval_base q1 x - (eval_base p1 x + x n * eval_base p2 x)))))%Z).
  apply Z.le_max_l.
  assumption.
  intros.
  rewrite ltb_is_neqb2 with (m := i) (n := j).
  reflexivity.
  apply leb_trans with (n := n0).
  assumption.
  assumption.
  rewrite <- H8.
  rewrite <- invariance_i with (p := q2) (i := n0) (f := fun (j : nat) => if j =? n0 then n1 else x j).
  apply H6 with (n := n1).
  apply Z.le_trans with (m := (max x0 (succ (abs (eval_base q1 x - eval_base (Poly p1 n p2) x))))%Z).
  apply Z.le_max_l.
  assumption.
  assumption.
  intros.
  elim (j =? n0).
  reflexivity.
  reflexivity.
  assumption.
  intros.
  rewrite ltb_is_neqb2 with (m := i) (n := j).
  rewrite ltb_is_neqb2 with (m := n0) (n := j).
  reflexivity.
  assumption.
  apply leb_trans with (n := S n0).
  assumption.
  assumption.
  simpl valid_bool_i in H.
  apply Bool.andb_true_iff in H.
  destruct H.
  simpl valid_bool_i.
  apply Bool.andb_true_iff.
  split.
  apply Nat_utils.leb_refl.
  assumption.
  intros.
  rewrite ltb_is_neqb2 with (m := i) (n := j).
  rewrite ltb_is_neqb2 with (m := n0) (n := j).
  reflexivity.
  apply leb_trans with (n := n).
  assumption.
  assumption.
  apply leb_trans with (n := n).
  apply leb_trans with (n := S n0).
  assumption.
  assumption.
  assumption.

  simpl valid_bool_i in H.
  apply Bool.andb_true_iff in H.
  destruct H.
  apply Bool.andb_true_iff in H3.
  destruct H3.
  apply Bool.andb_true_iff in H4.
  destruct H4.
  simpl valid_bool_i in H0.
  apply Bool.andb_true_iff in H0.
  destruct H0.
  apply Bool.andb_true_iff in H6.
  destruct H6.
  apply Bool.andb_true_iff in H7.
  destruct H7.
  destruct excluded_middle_poly with (p := p2) (q := q2).
  destruct excluded_middle_poly with (p := p1) (q := q1).
  destruct H1.
  apply f_equal3 with (f := Poly).
  assumption.
  assumption.
  assumption.
  destruct IHp1 with (i := i) (q := q1).
  apply valid_leb with (n := S n).
  apply leb_trans with (n := n).
  assumption.
  apply leb_succ.
  assumption.
  apply valid_leb with (n := S n0).
  apply leb_trans with (n := n0).
  assumption.
  apply leb_succ.
  assumption.
  assumption.
  destruct H11.
  exists x.
  exists x0.
  intros.
  rewrite <- H2.
  rewrite <- H9.
  simpl eval_base.
  intro.
  apply f_equal with (f := fun (y : Z) => (y - (if (n =? i)%nat then n1 else x n) * eval_base p2 (fun j : nat => if (j =? i)%nat then n1 else x j))%Z) in H13.
  revert H13.
  rewrite Z.add_simpl_r.
  rewrite Z.add_simpl_r.
  apply H11 with (n := n1).
  assumption.
  rewrite <- H2.
  destruct IHp2 with (i := n) (q := q2).
  assumption.
  rewrite H2.
  assumption.
  assumption.
  destruct H10.
  exists (fun (j : nat) => if j =? n then (max x0 (succ (abs (eval_base p1 x - eval_base q1 x))))%Z else x j).
  exists (max x0 (succ (abs (eval_base p1 x - eval_base q1 x))))%Z.
  intros.
  simpl eval_base.
  rewrite <- invariance_i with (p := p1) (i := S n) (f := x) (g := fun (j : nat) =>
   if j =? i then n1 else if j =? n then (max x0 (succ (abs (eval_base p1 x - eval_base q1 x))))%Z else x j).
  rewrite <- invariance_i with (p := q1) (i := S n) (f := x) (g := fun (j : nat) =>
   if j =? i then n1 else if j =? n then (max x0 (succ (abs (eval_base p1 x - eval_base q1 x))))%Z else x j).
  rewrite Nat.eqb_refl with (x := n).
  intro.
  apply f_equal with (f := fun (y : Z) => (y-(eval_base q1 x +
       (if (n =? i)%nat then n1 else max x0 (succ (abs (eval_base p1 x - eval_base q1 x)))) *
       eval_base q2
         (fun j : nat =>
          if (j =? i)%nat
          then n1
          else if (j =? n)%nat then max x0 (succ (abs (eval_base p1 x - eval_base q1 x))) else x j)))%Z) in H12.
  revert H12.
  rewrite Z.sub_diag.
  rewrite <- Z.add_opp_r.
  rewrite Z.opp_add_distr.
  rewrite Z.add_assoc.
  rewrite <- Z.add_assoc with (p := (- eval_base q1 x)%Z).
  rewrite Z.add_comm with (m := (- eval_base q1 x)%Z).
  rewrite Z.add_assoc with (m := (- eval_base q1 x)%Z).
  rewrite Z.add_opp_r with (n := eval_base p1 x).
  rewrite <- Z.add_assoc.
  rewrite Z.add_opp_r.
  rewrite <- Z.mul_sub_distr_l with (n := if (n =? i)%nat then n1 else max x0 (succ (abs (eval_base p1 x - eval_base q1 x)))).
  apply z_abs_lt.
  elim (n =? i).
  apply Z.lt_le_trans with (m := (succ (abs (eval_base p1 x - eval_base q1 x)))%Z).
  apply Z.lt_succ_diag_r.
  apply Z.le_trans with (m := (max x0 (succ (abs (eval_base p1 x - eval_base q1 x))))%Z).
  apply Z.le_max_r.
  assumption.
  apply Z.lt_le_trans with (m := (succ (abs (eval_base p1 x - eval_base q1 x)))%Z).
  apply Z.lt_succ_diag_r.
  apply Z.le_max_r.
  destruct ltb_compare_dec with (m := n) (n := i).
  exfalso.
  revert H12.
  apply Bool.not_true_iff_false.
  apply ltb_leb.
  assumption.
  destruct H12.
  rewrite <- invariance_i with (p := p2) (i := n) (f := fun (j : nat) => if (j =? n) then max x0 (succ (abs (eval_base p1 x - eval_base q1 x))) else x j).
  rewrite <- invariance_i with (p := q2) (i := n) (f := fun (j : nat) => if (j =? n) then max x0 (succ (abs (eval_base p1 x - eval_base q1 x))) else x j).
  intro.
  apply f_equal with (f := fun (y : Z) => (y + eval_base q2
         (fun j : nat => if (j =? n)%nat then max x0 (succ (abs (eval_base p1 x - eval_base q1 x))) else x j))%Z) in H13.
  revert H13.
  rewrite <- Z.add_opp_r.
  rewrite <- Z.add_assoc.
  rewrite Z.add_opp_diag_l.
  rewrite Z.add_0_r.
  rewrite Z.add_0_l.
  apply H10 with (n := (max x0 (succ (abs (eval_base p1 x - eval_base q1 x))))%Z).
  apply Z.le_max_l.
  rewrite H2.
  assumption.
  intros.
  rewrite ltb_is_neqb2 with (m := i) (n := j).
  reflexivity.
  apply leb_trans with (n := n).
  assumption.
  assumption.
  assumption.
  intros.
  rewrite ltb_is_neqb2 with (m := i) (n := j).
  reflexivity.
  apply leb_trans with (n := n).
  assumption.
  assumption.
  rewrite <- H12.
  rewrite <- invariance_i with (p := p2) (i := n) (f := fun (j : nat) => if j =? n then n1 else x j).
  rewrite <- invariance_i with (p := q2) (i := n) (f := fun (j : nat) => if j =? n then n1 else x j).
  intro.
  apply f_equal with (f := fun (y : Z) => (y + eval_base q2
         (fun j : nat => if (j =? n)%nat then n1 else x j))%Z) in H13.
  revert H13.
  rewrite <- Z.add_opp_r.
  rewrite <- Z.add_assoc.
  rewrite Z.add_opp_diag_l.
  rewrite Z.add_0_r.
  rewrite Z.add_0_l.
  apply H10 with (n := n1).
  apply Z.le_trans with (m := (max x0 (succ (abs (eval_base p1 x - eval_base q1 x))))%Z).
  apply Z.le_max_l.
  assumption. 
  rewrite H2.
  assumption.
  intros.
  elim (j =? n).
  reflexivity.
  reflexivity.
  assumption.
  intros.
  elim (j =? n).
  reflexivity.
  reflexivity.
  rewrite H2.
  assumption.
  intros.
  rewrite ltb_is_neqb2 with (m := i) (n := j).
  rewrite ltb_is_neqb2 with (m := n) (n := j).
  reflexivity.
  assumption.
  apply leb_trans with (n := S n).
  assumption.
  assumption.
  assumption.
  intros.
  rewrite ltb_is_neqb2 with (m := i) (n := j).
  rewrite ltb_is_neqb2 with (m := n) (n := j).
  reflexivity.
  assumption.
  apply leb_trans with (n := S n).
  assumption.
  assumption.
Qed.

Theorem eval_eq (p q : valid_poly) :
  (forall (f : nat -> Z), eval p f = eval q f) -> p = q.
Proof.
  destruct p as [p p'].
  destruct q as [q q'].
  unfold eval.
  simpl.
  intro.
  apply leibniz.
  simpl.
  destruct excluded_middle_poly with (p := p) (q := q).
  assumption.
  destruct diff_poly with (p := p) (q := q) (i := 0).
  assumption.
  assumption.
  assumption.
  destruct H1.
  contradiction H1 with (n := x0).
  apply Z.le_refl.
  apply H with (f := fun (j : nat) => if j =? 0 then x0 else x j).
Qed.
