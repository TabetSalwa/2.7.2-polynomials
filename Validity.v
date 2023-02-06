Require Import ZArith.

Inductive poly : Type :=
| Cst : Z -> poly
| Poly : poly -> nat -> poly -> poly.

(***********************************************)
(*         1. Multivariate Polynomials         *)
(***********************************************)


(*         1.1 Valid polynomials               *)

(* Question A *)
Definition is_null (p:poly) : bool :=
match p with
| Cst 0 => true
| _ => false
end.

Fixpoint is_valid_i (p':poly) (j:nat) : Prop :=
match p' with
| Cst z => True
| Poly p i q =>
  (Nat.leb j i) = true /\ (negb (is_null q)) = true /\ is_valid_i p (S i) /\ is_valid_i q i
end.

Definition is_valid (p:poly) : Prop :=
  is_valid_i p 0.

Eval compute in is_valid (Cst 3).
Eval compute in is_valid (Poly (Cst 1) 1 (Poly (Cst 0) 2 (Cst 2))).
Eval compute in is_valid (Poly (Cst 1) 1 (Poly (Cst 2) 2 (Cst 0))).
Eval compute in is_valid (Poly (Cst 1) 2 (Poly (Cst 0) 1 (Cst 2))).


(* Question B *)
Fixpoint valid_bool_i (p':poly) (j:nat) : bool :=
match p' with
| Cst z => true
| Poly p i q =>
  andb (Nat.leb j i) (andb (negb (is_null q)) (andb (valid_bool_i p (S i)) (valid_bool_i q i)))
end.

Definition valid_bool (p:poly) : bool :=
  valid_bool_i p 0.

Eval compute in valid_bool (Cst 3).
Eval compute in valid_bool (Poly (Cst 1) 1 (Poly (Cst 0) 2 (Cst 2))).
Eval compute in valid_bool (Poly (Cst 1) 1 (Poly (Cst 2) 2 (Cst 0))).
Eval compute in valid_bool (Poly (Cst 1) 2 (Poly (Cst 0) 1 (Cst 2))).

Lemma bool_equiv_ind_i (p : poly) (i : nat) :
  (valid_bool_i p i) = true <-> is_valid_i p i.
Proof.
  split.
  revert i.
  induction p.
  simpl.
  intro.
  trivial.

  simpl valid_bool_i.
  intro.
  intro.
  apply Bool.andb_true_iff in H.
  destruct H.
  apply Bool.andb_true_iff in H0.
  destruct H0.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  simpl is_valid_i.
  split.
  assumption.
  split.
  assumption.
  split.
  apply IHp1 with (i := S n).
  assumption.
  apply IHp2 with (i := n).
  assumption.

  revert i.
  induction p.
  simpl.
  intros.
  trivial.

  intro.
  intro.
  simpl is_valid_i in H.
  destruct H.
  destruct H0.
  destruct H1.
  simpl valid_bool_i.
  apply Bool.andb_true_iff.
  split.
  assumption.
  apply Bool.andb_true_iff.
  split.
  assumption.
  apply Bool.andb_true_iff.
  split.
  apply IHp1 with (i := S n).
  assumption.
  apply IHp2 with (i := n).
  assumption.
Qed.


Lemma bool_equiv_ind (p:poly) : 
  (valid_bool p) = true <-> is_valid p.
Proof.
  apply bool_equiv_ind_i with (i := 0).
Qed.


(* Question C *)
Record valid_poly : Type :=
{ VP_value : poly ;
  VP_prop : valid_bool  VP_value = true }.

Require Eqdep_dec.

Lemma proof_irrelevance (b:bool):
  forall (p1 p2 : b = true), p1 = p2.
Proof.
  intros.
  apply Eqdep_dec.eq_proofs_unicity.
  
  intros.
  elim x.
  elim y.
  left.
  reflexivity.
  right.
  intro H.
  discriminate H.

  elim y.
  right.
  intro H.
  discriminate H.

  left.
  reflexivity.
Qed.


Lemma leibniz (p q:valid_poly) : 
  VP_value p = VP_value q -> p = q.
Proof.
  destruct p as [p1 p2].
  destruct q as [q1 q2].
  simpl.
  intro.
  revert p2 q2.
  rewrite <- H.
  intros p2 q2.
  apply f_equal with (f := fun x => {| VP_value := p1; VP_prop := x |}).
  rewrite (proof_irrelevance (valid_bool p1) p2 q2).
  reflexivity.
Qed.