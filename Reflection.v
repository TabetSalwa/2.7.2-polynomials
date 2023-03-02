Require Import Nat_utils.
Require Import Validity.
Require Import ZArith. 
Require Import Coeff_utils.
Require Import Coeff.
Require Import Values.
Require Import Arith.

Fixpoint minus_base (p : poly) {struct p} : poly :=
  match p with
  |Cst (Z0) => Cst (Z0)
  |Cst (Z.pos z) => Cst (Z.neg z)
  |Cst (Z.neg z) => Cst (Z.pos z)
  |Poly p1 i p2 => Poly (minus_base p1) i (minus_base p2)
end.

Lemma minus_isnull (p : poly) :
  is_null p = is_null (minus_base p).
Proof.
  induction p.
  - induction z.
    + simpl minus_base.
      reflexivity.
    + simpl is_null.
      reflexivity.
    + simpl is_null.
      reflexivity.
  - simpl is_null.
    reflexivity.
Qed.

Lemma minus_valid_i (p : poly) :
  forall i : nat, valid_bool_i p i = true -> valid_bool_i (minus_base p) i = true.
Proof.
  induction p.
  induction z; simpl valid_bool_i; trivial.

  intros.
  simpl valid_bool_i in H.
  apply Bool.andb_true_iff in H.
  destruct H.
  apply Bool.andb_true_iff in H0.
  destruct H0.
  apply Bool.andb_true_iff in H1.
  destruct H1.

  simpl valid_bool_i.
  apply Bool.andb_true_iff.
  split.
  assumption.

  apply Bool.andb_true_iff.
  split.
  rewrite <- minus_isnull.
  assumption.

  apply Bool.andb_true_iff.
  split.
  apply IHp1.
  assumption.

  apply IHp2.
  assumption.

Qed.

Lemma minus_valid (p : poly) :
  valid_bool p = true -> valid_bool (minus_base p) = true.
Proof.
  unfold valid_bool.
  apply minus_valid_i with (i := 0).
  
Qed.

Definition minus_poly (p : valid_poly) : valid_poly :=
{| VP_value := minus_base (VP_value p) ;
   VP_prop := minus_valid (VP_value p) (VP_prop p) |}.

Theorem eval_minus (p : valid_poly) (f : nat -> Z) :
  eval (minus_poly p) f = Z.opp (eval p f).
Proof.
  destruct p as [p p'].
  unfold eval.
  simpl VP_value.
  induction p.

  - simpl.
    induction z;reflexivity.
  - unfold valid_bool in p'.
    simpl valid_bool_i in p'.
    apply Bool.andb_true_iff in p'.
    destruct p' as [p' p1'].
    apply Bool.andb_true_iff in p1'.
    destruct p1' as [p1' p2'].

    simpl eval_base.
    rewrite IHp1.
    rewrite IHp2.
    Lia.lia.

    unfold valid_bool; apply valid_leb with (n := n); trivial;assumption.
    unfold valid_bool; apply valid_leb with (n := S n); trivial;assumption.
Qed.




