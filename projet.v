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

(*
PREMIER JET
Definition mono : Type := list nat.

Fixpoint cst_term (p:poly) : Z :=
  match p with
  | Cst z => z
  | Poly q _ _ => cst_term q
end.

Fixpoint get_coef_i (p:poly) (m:mono) (i:nat) : Z :=
  match m with
  | nil => cst_term p
  | cons 0 t =>
    get_coef_i p t (S i)
  | cons (S h) t =>
    match p with
    | Cst _ => 0
    | Poly p' j q =>
    match Nat.compare i j with
      | Eq => get_coef_i q (cons h t) i
      | Lt => 0
      | Gt => get_coef_i p' m i
end end end. 

*)

Inductive mono : Type :=
  | One : mono
  | Mono : nat -> mono -> mono.

Fixpoint valid_mono_bool_i (m:mono) (i:nat) : bool :=
match m with
| One => true
| Mono j m' =>
  andb (Nat.leb i j) (valid_mono_bool_i m' j)
end.

Definition valid_mono_bool (m:mono) : bool :=
  valid_mono_bool_i m 0.


Fixpoint get_coeff_base (p:poly) (m:mono) : Z :=
  match m,p with
  | One, Cst z => z
  | One, Poly q _ _ => get_coeff_base q One
  | Mono _ _, Cst _ => 0
  | Mono i m', Poly p' j q =>
    match Nat.eqb i j with
    | true => get_coeff_base q m'
    | false => match Nat.ltb i j with
      | true => 0
      | false => get_coeff_base p' m
end end end.

Definition get_coeff (p:valid_poly) (m:mono) : Z :=
  get_coeff_base (VP_value p) m.



(*
Eval compute in get_coef (Cst 3) (One).
Eval compute in get_coef (Poly (Cst 1) 1 (Poly (Cst 0) 2 (Cst 2))) (Mono 1 One). 
Eval compute in get_coef (Poly (Cst 1) 1 (Poly (Cst 0) 2 (Cst 2))) (One).  
Eval compute in get_coef (Poly (Cst 1) 1 (Poly (Cst 0) 2 (Cst 2))) (Mono 1 (Mono 2 One)). 
*)

Lemma eqb_refl :
  forall (n : nat), (n =? n) = true.
Proof.
  induction n.
  simpl.
  reflexivity.
  simpl.
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

Lemma valid_succ :
  forall (p : poly) (i : nat),
  valid_bool_i p (S i) = true -> valid_bool_i p i = true.
Proof.
  intro p.
  elim p.

  intros.
  unfold valid_bool_i.
  reflexivity.

  intros.
  simpl.
  apply Bool.andb_true_iff.
  split.
  simpl valid_bool_i in H1.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  apply Bool.andb_true_iff in H2.
  destruct H2.
  revert H1.
  elim n.
  intro.
  discriminate H1.
  intros.
  apply leb_trans with (m := i) (n := n0) (p := S n0).
  assumption.
  apply leb_succ with (n := n0).

  apply Bool.andb_true_iff.
  split.
  simpl valid_bool_i in H1.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  apply Bool.andb_true_iff in H2.
  destruct H2.
  assumption.
  apply Bool.andb_true_iff.
  split.
  simpl valid_bool_i in H1.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  apply Bool.andb_true_iff in H2.
  destruct H2.
  apply Bool.andb_true_iff in H3.
  destruct H3.
  assumption.
  simpl valid_bool_i in H1.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  apply Bool.andb_true_iff in H2.
  destruct H2.
  apply Bool.andb_true_iff in H3.
  destruct H3.
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

Lemma valid_leb :
  forall (p : poly) (m n : nat),
  (m <=? n) = true -> valid_bool_i p n = true -> valid_bool_i p m = true.
Proof.
  intros.
  apply Bool.not_false_is_true.
  intro.
  revert H0.
  apply Bool.not_true_iff_false.
  apply rec_init with (P := fun i => valid_bool_i p i = false) (m := m) (n := n).
  intros.
  apply Bool.not_true_is_false.
  intro.
  revert  H0.
  apply Bool.not_false_iff_true.
  apply valid_succ with (p := p) (i := n0).
  assumption.
  assumption.
  assumption.
Qed.

Lemma exists_coeff (p q : poly) (i : nat) :
   valid_bool (Poly p i q) = true -> exists (m : mono), get_coeff_base (Poly p i q) (Mono i m) <> Z.zero.
Proof.
  intro.
  unfold valid_bool in H.
  simpl valid_bool_i in H.
  apply Bool.andb_true_iff in H.
  destruct H.
  apply Bool.andb_true_iff in H0.
  destruct H0.
  induction q.

  exists One.
  simpl.
  rewrite eqb_refl with (n := i).
  revert H.
  elim z.
  simpl.
  intro.
  discriminate H.
  simpl.
  intros.
  intro.
  discriminate H2.
  simpl.
  intros.
  intro.
  discriminate H2.

  simpl valid_bool_i in H1.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  apply Bool.andb_true_iff in H2.
  destruct H2.
  apply Bool.andb_true_iff in H3.
  destruct H3.

  destruct IHq2.
  assumption.
 

  simpl.
  apply valid_leb with (p := q2) (m := i) (n := n).
  assumption.
  assumption.

  exists (Mono n x).
  simpl.
  rewrite eqb_refl.
  rewrite eqb_refl.
  simpl in H5.
  rewrite eqb_refl in H5.
  assumption.
Qed.

Lemma  coeff_poly :
  forall (p1 p2 q1 q2 : poly) (i : nat) (m : mono),
  valid_bool (Poly p1 i p2) = true ->
  valid_bool (Poly q1 i q2) = true ->
  (get_coeff_base (Poly p1 i p2) m) = (get_coeff_base (Poly q1 i q2) m) <->
  (get_coeff_base p1 m = get_coeff_base q1 m /\ get_coeff_base p2 m = get_coeff_base q2 m).
Proof.
Admitted.


Lemma eq_coeff (p q:valid_poly) :
  (forall (m:mono), get_coeff p m = get_coeff q m) -> p = q.
Proof.
  intros.
  apply leibniz.
  destruct p as [p p'].
  destruct q as [q q'].
  unfold VP_value.
  unfold get_coeff in H.
  unfold VP_value in H.

  revert q H p' q'.
  induction p.

  induction q.
  simpl.
  intros.
  apply f_equal with (f := Cst).
  apply H with (m := One).

  intros.
  destruct exists_coeff with (p := q1) (q := q2) (i := n).
  assumption.
  exfalso.
  apply H0.
  symmetry.
  apply H with (m := Mono n x).

  induction q.
  intros.
  destruct exists_coeff with (p := p1) (q := p2) (i := n).
  assumption.
  exfalso.
  apply H0.
  apply H with (m := Mono n x).

  intros.
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
  apply f_equal3 with (f := Poly).

