Require Import AB.Imp8.
Require Import AB.Denotation.
Require Import AB.HoareLogic.

Open Scope list_scope.

Import Assertion_D.
Export Abstract_Pretty_Printing.

Import Command_Denotation_With_Steps.
Import Hoare_Logic.

Definition valid (Tr: hoare_triple): Prop :=
  match Tr with
  | Build_hoare_triple P c Q T =>
      exists a1 a2 N, 0 < a1 /\ 0 < a2 /\ 0 < N /\
      forall La st1 st2 t,
        (st1, La) |== P ->
        ceval c st1 t st2 ->
        ((st2, La) |== Q) /\ ab_eval La T a1 a2 N t
  end.

Notation "|==  Tr" := (valid Tr) (at level 91, no associativity).

(** Soundness Proof *)

Lemma hoare_skip_sound : forall P n,
  |== {{P}} Skip {{P}} $ BigTheta nil n.
Proof.
  unfold valid.
  exists 1, 1, 1.
  
  split. omega.
  split. omega.
  split. omega.
  
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
    simpl. omega.
  }
Qed.

Lemma Assertion_sub_spec: forall st1 st2 La (P: Assertion) (X: var) (E: aexp'),
  st2 X = aexp'_denote (st1, La) E ->
  (forall Y : var, X <> Y -> st1 Y = st2 Y) ->
  ((st1, La) |== P[ X |-> E]) <-> ((st2, La) |== P).
(* FILL IN HERE *) Admitted.

Lemma hoare_asgn_bwd_sound : forall P (X: var) (E: aexp) n,
  |== {{ P [ X |-> E] }} X ::= E {{ P }} $ BigTheta (1::nil) n.
Proof.
  unfold valid.
  exists 1, 1, 1.
  
  split. omega.
  split. omega.
  split. omega.
  
  intros.
  simpl in *.
  destruct H0, H1.
  split.
  {
    pose proof aeval_aexp'_denote st1 La E.
    rewrite H3 in H0.
    pose proof Assertion_sub_spec st1 st2 _ P _ _ H0 H1.
    tauto.
  }
  {
    intros.
    omega.
  }
Qed.

Lemma hoare_seq_sound_bigtheta : forall (P Q R: Assertion) (c1 c2: com) (p1 p2 : poly) (n : logical_var),
  |== {{P}} c1 {{Q}} $ BigTheta p1 n ->
  |== {{Q}} c2 {{R}} $ BigTheta p2 n ->
  |== {{P}} c1;;c2 {{R}} $ BigTheta (poly_add p1 p2) n.
Proof.
  unfold valid.
  intros.
  destruct H as [a1 [a2 [N [h1 [h2 [h3 ?]]]]]].
  destruct H0 as [a1' [a2' [N' [h1' [h2' [h3' ?]]]]]].
  simpl in *.
  exists (Z.min a1 a1'), (Z.max a2 a2'), (Z.max N N').
  
  split. apply (Z.min_glb_lt _ _ _ h1 h1').
  split. pose proof Z.le_max_l a2 a2'. omega.
  split. pose proof Z.le_max_l N N'. omega.
  
  intros.
  unfold seq_sem in H2.
  destruct H2 as [t1 [t2 [st3 [? [? ?]]]]].
  specialize (H _ _ _ _ H1 H2) as [? ?].
  specialize (H0 _ _ _ _ H H3) as [? ?].
  split.
  {
    exact H0.
  }
  {
    intros.
    pose proof Z.max_lub_l _ _ _ H7;
    pose proof Z.max_lub_r _ _ _ H7;
    clear H7.
    specialize (H5 H8); clear H8.
    specialize (H6 H9); clear H9.
    clear H1 H2 H3 H H0.
    destruct H5, H6.
    remember H4 as H5; clear HeqH5 H4.
    destruct H, H1.
    remember (poly_eval p1 (La n)) as T1.
    remember (poly_eval p2 (La n)) as T2.
    pose proof H as H'.
    rewrite (Z.mul_nonneg_cancel_l _ _ h1) in H'.
    pose proof H1 as H1'.
    rewrite (Z.mul_nonneg_cancel_l _ _ h1') in H1'.
    assert (0 <= a1' * T1). apply Z.mul_nonneg_nonneg; omega.
    assert (0 <= a1 * T2). apply Z.mul_nonneg_nonneg; omega.
    split.
    - rewrite poly_add_eval_comm, Z.mul_add_distr_l.
      rewrite <- HeqT1. rewrite <- HeqT2.
      pose proof Z.mul_min_distr_nonneg_r a1 a1' _ H'.
      pose proof Z.mul_min_distr_nonneg_r a1 a1' _ H1'.
      rewrite <- H8; clear H8.
      rewrite <- H9; clear H9.
      pose proof Z.min_glb _ _ _ H H6.
      pose proof Z.min_glb _ _ _ H7 H1.
      pose proof Z.le_min_l (a1 * T1) (a1' * T1).
      pose proof Z.le_min_r (a1 * T2) (a1' * T2).
      omega.
    - rewrite poly_add_eval_comm, Z.mul_add_distr_l.
      rewrite <- HeqT1. rewrite <- HeqT2.
      pose proof Z.mul_max_distr_nonneg_r a2 a2' _ H'.
      pose proof Z.mul_max_distr_nonneg_r a2 a2' _ H1'.
      rewrite <- H8; clear H8.
      rewrite <- H9; clear H9.
      pose proof Z.le_max_l (a2 * T1) (a2' * T1).
      pose proof Z.le_max_r (a2 * T2) (a2' * T2).
      omega.
  }
Qed.
(** [] *)
