Require Import AB.Imp8.
Require Import AB.HoareLogic.

Import Assertion_D.
Import Abstract_Pretty_Printing.
Import Hoare_Logic.

Module Slow_Addition_Demo.

Definition X : var := 0%nat.
Definition Y : var := 1%nat.

Fact slow_addition_correct (F: FirstOrderLogic): forall (m n : logical_var),
  |-- {{ {[X]} == m AND {[Y]} == n AND 0 <= m}}
      While !(X == 0) Do
        Y ::= Y + 1;;
        X ::= X - 1
      EndWhile
      {{ {[Y]} == m + n }}
      $ BigTheta LINEAR m.
Proof.
(* TODO: Fill in here *)
Admitted.

End Slow_Addition_Demo.

Module Min_While_Demo.

Definition A : var := 0%nat.
Definition B : var := 1%nat.
Definition C : var := 2%nat.

Fact min_while_correct (F: FirstOrderLogic): forall (a b : Z) (n : logical_var),
  |-- {{ {[A]} == a AND {[B]} == b AND 0 <= a AND 0 <= b AND n == Z.min a b }}
      C ::= 0;;
      While (! (A == 0) && ! (B == 0)) Do
        A ::= A - 1;;
        B ::= B - 1;;
        C ::= C + 1
      EndWhile
      {{ {[C]} == a AND a <= b OR {[C]} == b AND b < a }}
      $ BigO LINEAR n.
Proof.
(* TODO: Fill in here *)
Admitted.

End Min_While_Demo.
