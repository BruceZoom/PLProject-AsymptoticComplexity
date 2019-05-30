Require Import AB.Imp8.
Require Import Coq.ZArith.ZArith.

Open Scope Z.

Module Polynomial.

(* TODO: Implement polynomial type *)
Inductive poly : Type.

(* TODO: Implement polynomial evaluation *)
Fixpoint poly_eval (p : poly) : Z -> Z :=
  fun z => z.

Fixpoint poly_add (p1 p2 : poly) : poly := p1.

Fixpoint poly_mult (p1 p2 : poly) : poly := p1.

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

End Polynomial_Asympotitic_Bound.
