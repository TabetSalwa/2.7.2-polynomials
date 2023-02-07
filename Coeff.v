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

Record valid_mono : Type :=
{ VM_value : mono ;
VM_prop : valid_mono_bool VM_value = true}.

Remark vm_value_simpl (m : mono) (p : valid_mono_bool m = true) :
  m = VM_value {| VM_value :=m ; VM_prop := p|}.
Proof.
  reflexivity.
Qed.
  

Remark valid_mono_eq (P : mono -> Prop) :
  (forall (m : valid_mono), P (VM_value m)) <->
  (forall (m : mono), valid_mono_bool m = true -> P m).
Proof.
  split.
  intros.
  apply H with (m := {| VM_value := m; VM_prop := H0 |}).
  intros.
  destruct m as [m m'].
  apply H with (m := m).
  assumption.
Qed.

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

Definition get_coeff (p:valid_poly) (m: valid_mono) : Z :=
  get_coeff_base (VP_value p) (VM_value m).


Lemma exists_coeff_i (p q : poly) (i j : nat):
   valid_bool_i (Poly p i q) j = true -> exists (m : mono), valid_mono_bool_i (Mono i m) j = true /\ get_coeff_base (Poly p i q) (Mono i m) <> Z.zero.
Proof.
  revert p i j.
  induction q.
  intros.
  simpl valid_bool_i in H.
  apply Bool.andb_true_iff in H.
  destruct H.
  apply Bool.andb_true_iff in H0.
  destruct H0.
  apply Bool.andb_true_iff in H1.
  destruct H1.

  exists One.
  split.
  simpl.
  apply Bool.andb_true_iff.
  split.
  assumption.
  reflexivity.
  simpl.
  rewrite eqb_refl with (n := i).
  revert H0.
  elim z.
  simpl.
  intro.
  discriminate H0.
  simpl.
  intros.
  intro.
  discriminate H3.
  simpl.
  intros.
  intro.
  discriminate H3.

  intros.
  simpl valid_bool_i in H.
  apply Bool.andb_true_iff in H.
  destruct H.
  apply Bool.andb_true_iff in H0.
  destruct H0.
  destruct IHq2 with (p := q1) (i := n) (j := i).
  assumption.
  apply Bool.andb_true_iff in H1.
  destruct H1.
  apply Bool.andb_true_iff in H3.
  destruct H3.
  apply Bool.andb_true_iff in H4.
  destruct H4.

  exists (Mono n x).
  split.
  simpl.
  apply Bool.andb_true_iff.
  split.
  assumption.
  apply Bool.andb_true_iff.
  split.
  assumption.
  destruct H2.
  simpl valid_mono_bool_i in H2.
  apply Bool.andb_true_iff in H2.
  destruct H2.
  assumption.
  destruct H2.
  
  unfold get_coeff_base.
  rewrite eqb_refl with (n := i).
  assumption.
Qed.

Lemma exists_coeff (p q : poly) (i : nat) :
   valid_bool (Poly p i q) = true -> exists (m : mono), valid_mono_bool (Mono i m) = true /\ get_coeff_base (Poly p i q) (Mono i m) <> Z.zero.
Proof.
  apply exists_coeff_i with (j := 0).
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

Lemma get_coeff_l (p q: poly) (i j : nat) (m : mono) :
  valid_bool (Poly p i q) = true ->
  (i <? j) = true ->
  get_coeff_base p (Mono j m) = get_coeff_base (Poly p i q) (Mono j m).
Proof.
  intros.
  simpl.
  rewrite eqb_symm with (m := i) (n := j).
  rewrite ltb_is_neqb with (m := i) (n := j).
  rewrite ltb_antisymm with (m := i) (n := j).
  reflexivity.
  assumption.
  assumption.
Qed.

Lemma get_coeff_r (p q: poly) (i : nat) (m : mono) :
  valid_bool (Poly p i q) = true ->
  get_coeff_base q m = get_coeff_base (Poly p i q) (Mono i m).
Proof.
  intros.
  simpl.
  rewrite eqb_refl with (n := i).
  reflexivity.
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

Lemma valid_mono_mono (m : mono) (n : nat) :
  valid_mono_bool (Mono n m) = true <-> valid_mono_bool_i (Mono n m) n = true.
Proof.
  split.
  intro.
  simpl.
  apply Bool.andb_true_iff.
  split.
  apply leb_refl.
  unfold valid_mono_bool in H.
  simpl in H.
  assumption.

  intro.
  simpl in H.
  apply Bool.andb_true_iff in H.
  destruct H.
  unfold valid_mono_bool.
  simpl.
  assumption.
Qed.

Lemma valid_mono_leb (m : mono) (i j : nat) :
  (i <=? j) = true -> valid_mono_bool_i m j = true -> valid_mono_bool_i m i = true.
Proof. 
  revert i j.
  induction m.
  intros.
  reflexivity.
  intros.
  simpl.
  apply Bool.andb_true_iff.
  simpl in H0.
  apply Bool.andb_true_iff in H0.
  destruct H0.
  split.
  apply leb_trans with (n := j).
  assumption.
  assumption.
  assumption.
Qed.

Lemma  coeff_poly :
  forall (p1 p2 q1 q2 : poly) (i : nat),
  valid_bool (Poly p1 i p2) = true ->
  valid_bool (Poly q1 i q2) = true ->
  (forall (m : mono), valid_mono_bool m = true -> (get_coeff_base (Poly p1 i p2) m) = (get_coeff_base (Poly q1 i q2) m)) ->
  (forall (m : mono), valid_mono_bool m = true -> (get_coeff_base p1 m = get_coeff_base q1 m /\ get_coeff_base p2 m = get_coeff_base q2 m)).
Proof.
  intros.
  split.
  induction m.
  apply H1 with (m := One).
  assumption.
  destruct ltb_or_leb with (m := n) (n := i).
  rewrite get_coeff_l with (p := p1) (q := p2) (i := i) (j := n) (m := m).
  rewrite get_coeff_l with (p := q1) (q := q2) (i := i) (j := n) (m := m).
  apply H1 with (m := Mono n m).
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  rewrite null_coeff with (p := p1) (i := S i) (j := n) (m := m).
  rewrite null_coeff with (p := q1) (i := S i) (j := n) (m := m).
  reflexivity.
  unfold valid_bool in H0.
  apply Bool.andb_true_iff in H0.
  destruct H0.
  apply Bool.andb_true_iff in H4.
  destruct H4.
  apply Bool.andb_true_iff in H5.
  destruct H5.
  assumption.
  assumption.
  unfold valid_bool in H.
  apply Bool.andb_true_iff in H.
  destruct H.
  apply Bool.andb_true_iff in H4.
  destruct H4.
  apply Bool.andb_true_iff in H5.
  destruct H5.
  assumption.
  assumption.

  induction m.
  rewrite get_coeff_r with (p := p1) (q := p2) (i := i) (m := One).
  rewrite get_coeff_r with (p := q1) (q := q2) (i := i) (m := One).
  apply H1 with (m := (Mono i One)).
  unfold valid_mono_bool.
  reflexivity.
  assumption.
  assumption.
  destruct ltb_or_leb with (m := i) (n := n).
  rewrite null_coeff with (p := p2) (i := i) (j := n).
  rewrite null_coeff with (p := q2) (i := i) (j := n).
  reflexivity.
  unfold valid_bool in H0.
  apply Bool.andb_true_iff in H0.
  destruct H0.
  apply Bool.andb_true_iff in H4.
  destruct H4.
  apply Bool.andb_true_iff in H5.
  destruct H5.
  assumption.
  assumption.
  unfold valid_bool in H.
  apply Bool.andb_true_iff in H.
  destruct H.
  apply Bool.andb_true_iff in H4.
  destruct H4.
  apply Bool.andb_true_iff in H5.
  destruct H5.
  assumption.
  assumption.
  rewrite get_coeff_r with (p := p1) (q := p2) (i := i) (m := Mono n m).
  rewrite get_coeff_r with (p := q1) (q := q2) (i := i) (m := Mono n m).
  apply H1 with (m := Mono i (Mono n m)).
  unfold valid_mono_bool.
  apply Bool.andb_true_iff.
  split.
  reflexivity.
  apply Bool.andb_true_iff.
  split.
  assumption.
  assumption.
  assumption.
  assumption.
Qed.

Theorem eq_coeff (p q:valid_poly) :
  (forall (m : valid_mono), get_coeff p m = get_coeff q m) -> p = q.
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
  apply H with (m := {| VM_value := One; VM_prop := eq_refl true |}).

  intros.
  destruct exists_coeff with (p := q1) (q := q2) (i := n).
  assumption.
  exfalso.
  apply H0.
  symmetry.
  destruct H0.
  apply H with (m := {|VM_value := Mono n x; VM_prop := H0|}).

  induction q.
  intros.
  destruct exists_coeff with (p := p1) (q := p2) (i := n).
  assumption.
  exfalso.
  apply H0.
  destruct H0.
  apply H with (m := {|VM_value := Mono n x; VM_prop := H0|}).

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
  destruct m as [m m'].
  simpl.
  apply coeff_poly with (i := n) (p1 := p1) (q1 := q1) (p2 := p2) (q2 := q2) (m := m).
  assumption.
  assumption.
  intros.
  apply H with (m := {|VM_value := m0; VM_prop := H0 |}).
  assumption.

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
  destruct m as [m m'].
  simpl.
  apply coeff_poly with (i := n) (p1 := p1) (q1 := q1) (p2 := p2) (q2 := q2) (m := m).
  assumption.
  assumption.
  intros.
  apply H with (m := {|VM_value := m0; VM_prop := H0|}).
  assumption.

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
  destruct H1.
  apply H2.
  rewrite vm_value_simpl with (m := Mono n x) (p := H1).
  rewrite H with (m := {|VM_value := Mono n x; VM_prop := H1|}).
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
  destruct H1.
  apply H2.
  symmetry in H.
  rewrite vm_value_simpl with (m := Mono n0 x) (p := H1).
  rewrite H with (m := {|VM_value := Mono n0 x; VM_prop := H1|}).
  simpl.
  rewrite ltb_is_neqb.
  rewrite H0.
  reflexivity.
  assumption.
Qed.


