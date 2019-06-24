Require Import AB.Imp9.
Require Import AB.HoareLogic.

Import Assertion_D.
Import Abstract_Pretty_Printing.
Import Hoare_Logic.

Definition FOL_valid (P: Assertion): Prop :=
  forall J: Interp, J |== P.

Instance TrivialFOL: FirstOrderLogic :=
  {| FOL_provable := (fun P => FOL_valid P) |}.

Lemma convert_IMPLY : forall (P Q : Prop), (P -> Q) -> ~P \/ Q.
Proof.
  intros.
  pose proof excluded_middle P.
  destruct H0.
  - left. auto.
  - right. apply (H H0).
Qed.

Ltac entailer := 
    unfold derives, assn_sub;
    simpl; unfold FOL_valid;
    intros; simpl;
    apply convert_IMPLY;
    intros.

Lemma derives_refl: forall P, P |-- P.
Proof.
  intros.
  unfold derives, assn_sub.
  simpl.
  unfold FOL_valid.
  intros.
  simpl.
  apply excluded_middle.
Qed.

Lemma derives_trans: forall P Q R, P |-- Q -> Q |-- R -> P |-- R.
Proof.
  intros.
  unfold derives, assn_sub in *.
  simpl in *.
  unfold FOL_valid in *.
  intros.
  simpl in *. specialize (H J). specialize (H0 J).
  destruct H.
  - left. tauto.
  - destruct H0.
    + tauto.
    + right. tauto.
Qed.

Module Simple_Loop_Demo.

Definition X : var := 0%nat.

(* Lemma post_loop_body_der : forall (n : logical_var),
  0 <= {[X]} AND {[X]} == n - 1 |-- 0 <= {[X]} AND {[X]} == n - 1.
Proof.
  intros.
  entailer.
  auto.
Qed. *)

Lemma pre_loop_body_der : forall (n : logical_var),
  0 <= {[X]} AND {[(! (X == 0))%imp]} AND {[X]} == n
  |-- (0 <= {[X]} AND {[X]} == n - 1) [X |-> (X - 1)%imp].
Proof.
  entailer.
  omega.
Qed.

Fact simple_loop_correct : forall (n : logical_var),
  |-- {{ 0 <= {[X]} AND {[X]} == n }}
      While !(X == 0) Do
        X ::= X - 1
      EndWhile
      {{ 0 <= {[X]} AND NOT {[! (X == 0)]} }}
      $ BigO (LINEAR *** CONSTANT) n.
Proof.
  intros.
  apply (hoare_while_linear TrivialFOL); auto.
  - intros.
    simpl in *.
    omega.
  - intros.
    rewrite CONSTANT_spec.
    omega.
  - intros.
    rewrite CONSTANT_spec, CONSTANT_spec.
    omega.
  - apply hoare_loosen with (BigTheta CONSTANT n).
    apply Theta2O. simpl. omega.
    eapply hoare_consequence.
    3:{ apply derives_refl. }
    2:{ apply hoare_asgn_bwd. }
    apply pre_loop_body_der.
Qed.

End Simple_Loop_Demo.

Module Slow_Addition_Demo.

Definition X : var := 0%nat.
Definition Y : var := 1%nat.

Lemma pre_loop_der : forall m n,
  {[X]} == m AND {[Y]} == n AND 0 <= m |--
  {[X]} + {[Y]} == m + n AND 0 <= m AND {[X]} == m.
Proof.
  entailer.
  destruct H as [[? ?] ?].
  repeat split; auto; try omega.
Qed.

Fact slow_addition_correct : forall (m n : logical_var),
  |-- {{ {[X]} == m AND {[Y]} == n AND 0 <= m }}
      While !(X == 0) Do
        Y ::= Y + 1;;
        X ::= X - 1
      EndWhile
      {{ {[Y]} == m + n }}
      $ BigTheta LINEAR m.
Proof.
  intros.
  pose proof hoare_while_linear.
  
Admitted.

End Slow_Addition_Demo.

Module Min_While_Demo.

Definition A : var := 0%nat.
Definition B : var := 1%nat.
Definition C : var := 2%nat.

Fact min_while_correct: forall (a b : Z) (n : logical_var),
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
  intros.
  eapply hoare_consequence.
  apply derives_refl.
Admitted.

End Min_While_Demo.
