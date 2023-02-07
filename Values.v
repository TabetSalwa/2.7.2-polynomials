Require Import Nat_utils.
Require Import Validity.
Require Import ZArith. 
Require Import Coeff_utils.
Require Import Coeff.

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
