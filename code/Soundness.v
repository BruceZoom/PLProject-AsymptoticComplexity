Require Import AB.Imp8.
Require Import AB.Denotation.
Require Import AB.HoareLogic.

Import Assertion_D.
Export Abstract_Pretty_Printing.

Import Command_Denotation_With_Steps.
Import Hoare_Logic.

Definition valid (Tr: hoare_triple): Prop :=
  match Tr with
  | Build_hoare_triple P c Q T =>
      exists a1 a2 N,
      forall La st1 st2 t,
        (st1, La) |== P ->
        ceval c st1 t st2 ->
        ((st2, La) |== Q) /\ ab_eval La T a1 a2 N t
  end.

Notation "|==  Tr" := (valid Tr) (at level 91, no associativity).

(* The p should be 1 *)
Lemma hoare_skip_sound : forall P p n,
  |== {{P}} Skip {{P}} $ BigTheta p n.
Proof.
  unfold valid.
  exists 1, 1, 0.
  intros.
  simpl in H0.
  unfold skip_sem in H0.
  destruct H0.
  split.
  {
    rewrite <- H0.
    exact H.
  }
  {
    unfold ab_eval.
    intros.
    remember (La n) as n'.
    admit. (* after poly is fully defined *)
  }
Admitted.

Lemma hoare_seq_sound_bigtheta : forall (P Q R: Assertion) (c1 c2: com) (p1 p2 : poly) (n : logical_var),
  |== {{P}} c1 {{Q}} $ BigTheta p1 n ->
  |== {{Q}} c2 {{R}} $ BigTheta p2 n ->
  |== {{P}} c1;;c2 {{R}} $ BigTheta (poly_add p1 p2) n.
Admitted.
