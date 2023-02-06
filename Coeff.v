(*Add LoadPath "/home/stabet/Documents/MPRI2/2.7.2/polynomials"*)
Require Import Validity.
Require Import ZArith.
Require Import Nat_utils.
Require Import Coeff_utils.

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

Lemma simpl :
  forall (p q : poly) (i : nat) (m : mono),
  get_coeff_base (Poly p i q) (Mono i m) = get_coeff_base q m.
Proof.
  intros.
  simpl.
  rewrite eqb_refl.
  reflexivity.
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

Lemma null_coeff (p : poly) (i j : nat) (m : mono) :
  valid_bool_i p i = true ->
  (j <? i) = true ->
  get_coeff_base p (Mono j m) = Z.zero.
Proof.
  induction p.
  simpl.
  intros.
  reflexivity.
  intro.
  simpl valid_bool_i in H.
  apply Bool.andb_true_iff in H.
  destruct H.
  apply Bool.andb_true_iff in H0.
  destruct H0.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  intro.
  simpl.
  rewrite ltb_is_neqb.
  unfold Nat.ltb.
  rewrite leb_trans with (m := S j) (n := i) (p := n).
  reflexivity.
  assumption.
  assumption.
  unfold Nat.ltb.
  rewrite leb_trans with (m := S j) (n := i) (p := n).
  reflexivity.
  assumption.
  assumption.
Qed.

Lemma  coeff_poly :
  forall (p1 p2 q1 q2 : poly) (i : nat),
  valid_bool (Poly p1 i p2) = true ->
  valid_bool (Poly q1 i q2) = true ->
  (forall (m : mono), (get_coeff_base (Poly p1 i p2) m) = (get_coeff_base (Poly q1 i q2) m)) <->
  (forall (m : mono), (get_coeff_base p1 m = get_coeff_base q1 m /\ get_coeff_base p2 m = get_coeff_base q2 m)).
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
  pose proof H.
  pose proof q'.
  revert H0 H1.
  rewrite leb_antisymm with (n := n) (m := n0).
  clear H q'.
  intros H q'.
  apply f_equal3 with (f := Poly).
  apply IHp1 with (q := q1).
  intro.
  apply coeff_poly with (i := n) (p1 := p1) (q1 := q1) (p2 := p2) (q2 := q2) (m := m).
  assumption.
  assumption.
  intro.
  apply H with (m := m0).
  unfold valid_bool in p'.
  simpl valid_bool_i in p'.
  apply Bool.andb_true_iff in p'.
  destruct p'.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  unfold valid_bool.
  apply valid_leb with (p := p1) (m := 0) (n := S n).
  simpl.
  reflexivity.
  assumption.
  unfold valid_bool in q'.
  simpl valid_bool_i in q'.
  apply Bool.andb_true_iff in q'.
  destruct q'.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  apply valid_leb with (p := q1) (m := 0) (n := S n).
  simpl.
  reflexivity.
  assumption.
  reflexivity.
  apply IHp2 with (q := q2).
  intro.
  apply coeff_poly with (i := n) (p1 := p1) (q1 := q1) (p2 := p2) (q2 := q2) (m := m).
  assumption.
  assumption.
  intro.
  apply H with (m := m0).

  unfold valid_bool in p'.
  simpl valid_bool_i in p'.
  apply Bool.andb_true_iff in p'.
  destruct p'.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  unfold valid_bool.
  apply valid_leb with (p := p2) (m := 0) (n := n).
  simpl.
  reflexivity.
  assumption.
  unfold valid_bool in q'.
  simpl valid_bool_i in q'.
  apply Bool.andb_true_iff in q'.
  destruct q'.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  apply valid_leb with (p := q2) (m := 0) (n := n).
  simpl.
  reflexivity.
  assumption.

  apply ltb_leb.
  apply Bool.not_true_is_false.
  intro.

  destruct exists_coeff with (p := p1) (q := p2) (i := n).
  assumption.
  apply H1.
  rewrite H with (m := Mono n x).
  simpl.
  rewrite ltb_is_neqb.
  rewrite H0.
  reflexivity.
  assumption.

  apply ltb_leb.
  apply Bool.not_true_is_false.
  intro.

  destruct exists_coeff with (p := q1) (q := q2) (i := n0).
  assumption.
  apply H1.
  symmetry in H.
  rewrite H with (m := Mono n0 x).
  simpl.
  rewrite ltb_is_neqb.
  rewrite H0.
  reflexivity.
  assumption.
Qed.