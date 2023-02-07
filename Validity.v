Require Import ZArith.
Require Import Nat_utils.

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

Inductive is_valid_i : poly -> nat -> Prop :=
| Is_valid_cst z i : is_valid_i (Cst z) i
| Is_valid_poly p n q i : n >= i /\ q <> Cst 0 /\ is_valid_i p (S n) /\ is_valid_i q n -> is_valid_i (Poly p n q) i.
 
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
  intros.
  apply Is_valid_cst.

  simpl valid_bool_i.
  intro.
  intro.
  apply Bool.andb_true_iff in H.
  destruct H.
  apply Bool.andb_true_iff in H0.
  destruct H0.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  apply Is_valid_poly.
  split.
  apply Nat.leb_le.
  assumption.
  split.
  intro.
  rewrite H3 in H0.
  simpl in H0.
  discriminate H0.
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
  inversion H.
  destruct H4.
  destruct H5.
  destruct H6.
  simpl valid_bool_i.
  apply Bool.andb_true_iff.
  split.
  apply Nat.leb_le.
  assumption.
  apply Bool.andb_true_iff.
  split.
  apply Bool.negb_true_iff.
  apply Bool.not_true_is_false.
  intro.
  apply H5.
  revert H8.
  elim p2.
  simpl.
  intro.
  elim z.
  intro.
  reflexivity.
  intros.
  discriminate H8.
  intros.
  discriminate H8.
  simpl.
  intros.
  discriminate H10.
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

Lemma bool_dec (b b' : bool) : b = b' \/ b <> b'.
Proof.
  case b.
  case b'.
  left.
  reflexivity.
  right.
  intro.
  discriminate H.
  case b'.
  right.
  intro.
  discriminate H.
  left.
  reflexivity.
Qed.

Definition comp (b b1 b2 : bool) (eq1 : b = b1) (eq2 : b = b2) : b1 = b2 :=
    eq_trans (eq_sym eq1) eq2.

Lemma trans_sym_eq (b1 b2 : bool) (u : b1 = b2) : comp b1 b2 b2 u u = eq_refl b2.
Proof.
  case u.
  trivial.
Qed.

Definition nu (u : true = true) : true = true :=
match bool_dec true true with
  | or_introl eq => eq
  | or_intror neq => False_ind _ (neq u)
end.

Definition nu_constant (u v : true = true) : nu u = nu v.
  unfold nu.
  destruct (bool_dec true true) as [Heq|Hneq].
  reflexivity.
  case Hneq.
Qed.

Definition nu_inv (u : true = true) := comp true true true (nu (eq_refl true)) u.

Lemma nu_injective (u : true = true) : u = nu_inv (nu u).
Proof.
  symmetry.
  unfold nu_inv.
  unfold nu.
  case u.
  apply trans_sym_eq.
Qed.

Lemma proof_irrelevance (b:bool):
  forall (p1 p2 : b = true), p1 = p2.
Proof.
  case b.
  intros.
  rewrite nu_injective with (u := p1).
  rewrite nu_injective with (u := p2).
  apply f_equal with (f := nu_inv).
  apply nu_constant.
  intro.
  discriminate p1.
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