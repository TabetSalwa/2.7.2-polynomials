Require Import Nat_utils.
Require Import Validity.
Require Import ZArith. 
Require Import Coeff_utils.
Require Import Coeff.
Require Import Values.

(*         1.3 Arithmetic Operations           *)


(* Question 1.3.a *)

From Equations Require Import Equations.

(*Equations sum_poly (p : poly) (q : poly) {struct p}: poly :=
  match p,q with
  |Cst z1, Cst z2 => Cst (z1 + z2)
  |Cst z1 as c, Poly q1 j q2 as q => sum_poly q c (*Poly (sum_poly q1 c) j q2*)
  |Poly p1 i p2, Cst z2 as c => Poly (sum_poly p1 c) i p2
  |Poly p1 i p2, Poly q1 j q2 => 
    match Nat.compare i j with
    | Eq => Poly (sum_poly p1 q1) i (sum_poly p2 q2)
    | Lt => Poly (sum_poly p1 (Poly q1 j q2)) i p2
    | Gt => fun p Poly (sum_poly (Poly p1 i p2) q1) j q2
    end
end.*)

Equations sum_poly (p q : poly) : poly :=
  sum_poly (Cst z1) (Cst z2) := Cst (z1 + z2);
  sum_poly (Cst z1) (Poly q1 j q2) := Poly (sum_poly q1 (Cst z1)) j q2;
  sum_poly (Poly p1 i p2) (Cst z2) := Poly (sum_poly p1 (Cst z2)) i p2;
  sum_poly (Poly p1 i p2) (Poly q1 j q2) := 
    match Nat.compare i j with
    | Eq => Poly (sum_poly p1 q1) i (sum_poly p2 q2)
    | Lt => Poly (sum_poly p1 (Poly q1 j q2)) i p2
    | Gt => Poly (sum_poly (Poly p1 i p2) q1) j q2
    end.

