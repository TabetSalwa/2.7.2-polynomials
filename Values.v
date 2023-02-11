Require Import Nat_utils. 
Require Import Validity.
Require Import ZArith. 
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

Lemma poly_null_iff (p : poly) (i : nat) :
  valid_bool_i p i = true ->
  (forall (f : nat -> Z), f i <> Z.zero -> eval_base p f = Z.zero) ->
  is_null p = true.
Proof.
  revert i.
  induction p.  
  intros.
  apply is_null_iff.
  apply f_equal with (f := Cst).
  apply H0 with (f := fun (i : nat) => Z.one).
  intro.
  discriminate H1.

  intros.
  simpl valid_bool_i in H.
  apply Bool.andb_true_iff in H.
  destruct H.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  apply Bool.andb_true_iff in H2.
  destruct H2.
  apply Bool.negb_true_iff in H1.
  apply Bool.not_true_iff_false in H1.
  exfalso.
  apply H1.
  apply IHp2 with (i := n).
  assumption.
  intros.
  destruct z_integrity with (m := f n) (n := eval_base p2 f).
  destruct H5.
  apply add_simpl with (p := eval_base p1 f).
  rewrite add_comm.
  destruct IHp1 with (i := n).
  apply valid_succ.
  assumption.
  
  intros.
  rewrite invariance_i with (p := p1) (i := S n) (f := f0) (g := fun (j : nat) => if j <=? n then Z.zero else f0 n).
Admitted.

Lemma constant_is_constant (p : valid_poly) (z : Z) :
  (forall (f : nat -> Z), eval p f = z) -> VP_value p = Cst z.
Proof.
  destruct p as [p p'].
  revert z.
  induction p.
  intros.
  simpl.
  apply f_equal with (f := Cst).
  apply H with (f := zeros).

  intros.
  exfalso.
  unfold valid_bool in p'.
  simpl valid_bool_i in p'.
  unfold eval in H.
  simpl in H.
  unfold eval in IHp1.
  simpl in IHp1.
  unfold eval in IHp2.
  simpl in IHp2.
  apply Bool.andb_true_iff in p'.
  destruct p'.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  apply Bool.negb_true_iff in H0.
  apply Bool.not_true_iff_false in H0.
  apply H0.
  apply is_null_iff.
  apply IHp2 with (z := Z.zero).
  apply valid_leb with (p := p2) (m := 0) (n := n).
  reflexivity.
  assumption.
  intro.
  
  (*apply IHp2 with (z := Z.zero).*)
Admitted.

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
  revert q q' H.
  induction p.
  induction q.
Admitted.
