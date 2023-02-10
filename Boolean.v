Require Import ZArith. 

Open Scope bool_scope.

Inductive BTerm := 
| BTconst : bool -> BTerm
| BTvar : nat -> BTerm
| BTnot : BTerm -> BTerm
| BTand : BTerm -> BTerm -> BTerm
| BTor : BTerm -> BTerm -> BTerm.


Fixpoint eval_BTerm (f : BTerm) (v : nat -> bool) : bool :=
  match f with
  | BTconst b => b
  | BTvar n => v n
  | BTand f1 f2 => andb (eval_BTerm f1 v) (eval_BTerm f2 v)
  | BTor f1 f2 => orb (eval_BTerm f1 v) (eval_BTerm f2 v)
  | BTnot f1 => negb (eval_BTerm f1 v)
  end.

From Coq Require Import List.
Import ListNotations.

Ltac list_add a l :=
  let rec aux a l n :=
    match l with
    | []       => constr:((n, a :: l))
    | a :: _   => constr:((n,l))
    | ?x :: ?l => 
      match aux a l (S n) with
      | (?n, ?l) => constr:((n, x :: l))
      end
    end in
   aux a l 0.

Ltac read_term f l :=
  match f with
  | true => constr:((BTconst true, l))
  | false => constr:((BTconst false, l))
  | negb ?x =>
    match read_term x l with
    | (?x', ?l') => constr:((BTnot x', l'))
    end
  | andb ?x ?y => 
    match read_term x l with
    | (?x', ?l') => 
      match read_term y l' with
      | (?y', ?l'') => constr:((BTand x' y', l''))
      end
    end
  | orb ?x ?y => 
    match read_term x l with
    | (?x', ?l') => 
      match read_term y l' with
      | (?y', ?l'') => constr:((BTor x' y', l''))
      end
    end
  | _ =>
    match list_add f l with 
      | (?n, ?l') => constr:((BTvar n, l'))
    end
  end.

Goal forall a : bool, True.
  intros a.
  let v := read_term (andb (negb (negb a)) (negb (negb a))) (@nil bool) in
  idtac v.
Abort.