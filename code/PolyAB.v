Require Import AB.Imp8.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Open Scope Z.

Module Polynomial.
Import Assertion_D.
Open Scope term_scope.

(* TODO: Implement polynomial type *)
Definition poly := list (Z * nat).

(* TODO: Implement polynomial evaluation *)
Fixpoint poly_eval (n : nat) (p : poly) :Z :=
  match p with
  | nil => 0
  | (k, o)::tail => k * (Zpower_nat (Z.of_nat n) o) + (poly_eval n tail)
  end.

Print aexp'.
(* TODO: Implement polynomial evaluation to aexp' *)
Fixpoint poly_eval_lv (p : poly) : logical_var -> term :=
  fun v => v+1.

(* TODO: Implement polynomial addition *)
Fixpoint poly_add (p1 p2 : poly) : poly :=
  let fix poly_add_aux (p2: poly) : poly :=
      match p1, p2 with
      | nil, nil => nil
      | _ , nil => p1
      | nil, _ => p2
      | (k,o)::t, (k', o')::t' =>
        match (Z.of_nat o) ?= (Z.of_nat o') with
        | Lt => (k', o')::(poly_add_aux t')
        | Eq => ((Z.add k k'), o)::(poly_add t t')
        | Gt => (k, o)::(poly_add t p2)
        end
      end in poly_add_aux p2.



(* TODO: Implement polynomial multiplication *)
Fixpoint poly_mult (p1 p2 : poly) : poly := p1.

Close Scope term_scope.
End Polynomial.

Module Polynomial_Asympotitic_Bound.
Export Polynomial.
Import Assertion_D.

Inductive AsymptoticBound : Type :=
  | BigO : poly -> logical_var -> AsymptoticBound
  | BigOmega : poly -> logical_var -> AsymptoticBound
  | BigTheta : poly -> logical_var -> AsymptoticBound.

Definition ab_eval (La : Lassn) (T : AsymptoticBound) (a1 a2 N t : Z) : Prop :=
  match T with
  | BigO p n => La n >= N ->
                0 <= t <= a2 * (poly_eval p (La n))
  | BigOmega p n => La n >= N ->
                    a1 * (poly_eval p (La n)) <= t
  | BigTheta p n => La n >= N ->
                    a1 * (poly_eval p (La n)) <= t <= a2 * (poly_eval p (La n))
  end.

Reserved Notation "T1 '=<' T2" (at level 50, no associativity).

Inductive loosen : AsymptoticBound -> AsymptoticBound -> Prop :=
  | Theta2Omega : forall p n, BigTheta p n =< BigOmega p n
  | Theta2O : forall p n, BigTheta p n =< BigO p n
  (* TODO: real loosenings *)
  
  where "T1 '=<' T2" := (loosen T1 T2).

End Polynomial_Asympotitic_Bound.
