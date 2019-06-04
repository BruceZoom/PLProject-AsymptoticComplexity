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
  |== {{P}} Skip {{P}} $ BigTheta CONSTANT n.
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
    rewrite CONSTANT_spec.
    omega.
  }
Qed.

Lemma Assertion_sub_spec: forall st1 st2 La (P: Assertion) (X: var) (E: aexp'),
  st2 X = aexp'_denote (st1, La) E ->
  (forall Y : var, X <> Y -> st1 Y = st2 Y) ->
  ((st1, La) |== P[ X |-> E]) <-> ((st2, La) |== P).
Proof.
  intros.
  split.
  {
    intros.
    (* TODO: Fill in here *)
    admit.
  }
Admitted.

Lemma hoare_asgn_bwd_sound : forall P (X: var) (E: aexp) n,
  |== {{ P [ X |-> E] }} X ::= E {{ P }} $ BigTheta CONSTANT n.
Proof.
  unfold valid.
  exists 1, 1, 1.
  
  split. omega.
  split. omega.
  split. omega.
  
  intros.
  simpl in H0.
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
    unfold ab_eval.
    rewrite CONSTANT_spec.
    omega.
  }
Qed.

Lemma hoare_seq_bigtheta_sound : forall (P Q R: Assertion) (c1 c2: com) (p1 p2 : poly) (n : logical_var),
  |== {{P}} c1 {{Q}} $ BigTheta p1 n ->
  |== {{Q}} c2 {{R}} $ BigTheta p2 n ->
  |== {{P}} c1;;c2 {{R}} $ BigTheta (p1 +++ p2) n.
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
    - rewrite poly_add_spec, Z.mul_add_distr_l.
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
    - rewrite poly_add_spec, Z.mul_add_distr_l.
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

Lemma command_cost_time : forall c st1 st2 t,
  ceval c st1 t st2 -> 0 < t.
Proof.
  intro.
  induction c; intros; simpl in H.
  - unfold skip_sem in H. omega.
  - unfold asgn_sem in H. omega.
  - unfold seq_sem in H.
    destruct H as [t1 [t2 [st3 [? [? ?]]]]].
    specialize (IHc1 st1 st3 t1 H).
    specialize (IHc2 st3 st2 t2 H0).
    omega.
  - unfold if_sem in H.
    destruct H as [[? ?] | [? ?]].
    + specialize (IHc1 st1 st2 (t-1) H). omega.
    + specialize (IHc2 st1 st2 (t-1) H). omega.
  - unfold loop_sem in H. destruct H as [n ?].
    generalize dependent t. revert st2. revert st1.
    induction n; intros.
    + simpl in H. omega.
    + simpl in H.
      destruct H.
      destruct H as [t1 [t2 [st3 [? [? ?]]]]].
      specialize (IHn _ _ _ H1).
      specialize (IHc _ _ _ H).
      omega.
Qed.

Lemma hoare_if_same_sound : forall P Q (b: bexp) c1 c2 T,
  |== {{ P AND {[b]} }} c1 {{ Q }} $ T ->
  |== {{ P AND NOT {[b]} }} c2 {{ Q }} $ T ->
  |== {{ P }} If b Then c1 Else c2 EndIf {{ Q }} $ T.
Proof.
  unfold valid.
  intros.
  destruct H as [a1 [a2 [N [h1 [h2 [h3 ?]]]]]].
  destruct H0 as [a1' [a2' [N' [h1' [h2' [h3' ?]]]]]].
  simpl in *.
  exists (Z.min a1 a1'), (2 * (Z.max a2 a2')), (Z.max N N').
  
  split. apply (Z.min_glb_lt _ _ _ h1 h1').
  split. pose proof Z.le_max_l a2 a2'. omega.
  split. pose proof Z.le_max_l N N'. omega.
  
  intros.
  unfold if_sem in H2.
  destruct H2 as [[? ?] | [? ?]].
  - (* if branch *)
    pose proof beval_bexp'_denote st1 La b.
    pose proof H La st1 st2 (t-1).
    split.
    {
      tauto.
    }
    {
      assert (ab_eval La T a1 a2 N (t - 1)) as HAB. tauto.
      pose proof command_cost_time _ _ _ _ H2 as HT.
      clear H H0 H1 H2 H3 H4 H5.
      destruct T;
      unfold ab_eval in *;
      intros;
      pose proof Z.max_lub_l _ _ _ H;
      pose proof Z.max_lub_r _ _ _ H;
      clear H;
      remember (poly_eval p (La l)) as T.
      - (* BigO *)
        pose proof HAB H0 as [? ?].
        assert (0 <= a2 * T). omega.
        rewrite (Z.mul_nonneg_cancel_l _ _ h2) in H3.
        rewrite <- Z.mul_assoc.
        rewrite <- (Z.mul_max_distr_nonneg_r _ _ _ H3).
        pose proof Z.le_max_l (a2 * T) (a2' * T).
        omega.
      - (* BigOmega *)
        pose proof HAB H0 as [? ?].
        pose proof H.
        rewrite (Z.mul_nonneg_cancel_l _ _ h1) in H3.
        rewrite <- (Z.mul_min_distr_nonneg_r _ _ _ H3).
        pose proof Z.le_min_l (a1 * T) (a1' * T).
        assert (0 <= a1' * T). apply Z.mul_nonneg_nonneg; omega.
        pose proof Z.min_glb _ _ _ H H5.
        omega.
      - (* BigTheta *)
        pose proof HAB H0 as [[? ?] ?].
        pose proof H.
        rewrite (Z.mul_nonneg_cancel_l _ _ h1) in H4.
        rewrite <- (Z.mul_min_distr_nonneg_r _ _ _ H4).
        rewrite <- Z.mul_assoc.
        rewrite <- (Z.mul_max_distr_nonneg_r _ _ _ H4).
        assert (0 <= a1' * T). apply Z.mul_nonneg_nonneg; omega.
        assert (0 <= a1 * T). apply Z.mul_nonneg_nonneg; omega.
        clear H4.
        split.
        + pose proof Z.le_min_l (a1 * T) (a1' * T).
          pose proof Z.min_glb _ _ _ H H5.
          omega.
        + pose proof Z.le_max_l (a2 * T) (a2' * T).
          assert (t <= 2 * t - 2).
          {
            rewrite <- Z.add_diag.
            rewrite <- Z.add_sub_assoc.
            rewrite <- Z.add_0_r at 1.
            apply Zplus_le_compat_l.
            omega.
          }
          omega.
    }
  - (* else branch *)
    pose proof beval_bexp'_denote st1 La b.
    pose proof H0 La st1 st2 (t-1).
    split.
    {
      tauto.
    }
    {
      assert (ab_eval La T a1' a2' N' (t - 1)) as HAB. tauto.
      pose proof command_cost_time _ _ _ _ H2 as HT.
      clear H H0 H1 H2 H3 H4 H5.
      destruct T;
      unfold ab_eval in *;
      intros;
      pose proof Z.max_lub_l _ _ _ H;
      pose proof Z.max_lub_r _ _ _ H;
      clear H;
      remember (poly_eval p (La l)) as T.
      - (* BigO *)
        pose proof HAB H1 as [? ?].
        assert (0 <= a2' * T). omega.
        rewrite (Z.mul_nonneg_cancel_l _ _ h2') in H3.
        rewrite <- Z.mul_assoc.
        rewrite <- (Z.mul_max_distr_nonneg_r _ _ _ H3).
        pose proof Z.le_max_r (a2 * T) (a2' * T).
        omega.
      - (* BigOmega *)
        pose proof HAB H1 as [? ?].
        pose proof H.
        rewrite (Z.mul_nonneg_cancel_l _ _ h1') in H3.
        rewrite <- (Z.mul_min_distr_nonneg_r _ _ _ H3).
        pose proof Z.le_min_r (a1 * T) (a1' * T).
        assert (0 <= a1 * T). apply Z.mul_nonneg_nonneg; omega.
        pose proof Z.min_glb _ _ _ H5 H.
        omega.
      - (* BigTheta *)
        pose proof HAB H1 as [[? ?] ?].
        pose proof H.
        rewrite (Z.mul_nonneg_cancel_l _ _ h1') in H4.
        rewrite <- (Z.mul_min_distr_nonneg_r _ _ _ H4).
        rewrite <- Z.mul_assoc.
        rewrite <- (Z.mul_max_distr_nonneg_r _ _ _ H4).
        assert (0 <= a1' * T). apply Z.mul_nonneg_nonneg; omega.
        assert (0 <= a1 * T). apply Z.mul_nonneg_nonneg; omega.
        clear H4.
        split.
        + pose proof Z.le_min_r (a1 * T) (a1' * T).
          pose proof Z.min_glb _ _ _ H6 H5.
          omega.
        + pose proof Z.le_max_r (a2 * T) (a2' * T).
          assert (t <= 2 * t - 2).
          {
            rewrite <- Z.add_diag.
            rewrite <- Z.add_sub_assoc.
            rewrite <- Z.add_0_r at 1.
            apply Zplus_le_compat_l.
            omega.
          }
          omega.
    }
Qed.

Lemma hoare_loosen_sound : forall P Q c T1 T2,
  T1 =< T2 ->
  |== {{P}} c {{Q}} $ T1 ->
  |== {{P}} c {{Q}} $ T2.
Proof.
  unfold valid.
  intros.
  destruct H0 as [a1 [a2 [N [h1 [h2 [h3 ?]]]]]].
(*  pose proof loosen_valid _ _ H as Hlv.*)
  induction H.
  (* Theta2Omega *)
  {
    exists a1, a2, N.
    intros.
    split. omega.
    split. omega.
    split. omega.
    intros.
    specialize (H0 La st1 st2 t H H1).
    split. tauto.
    destruct H0 as [_ ?].
    simpl in *. intros.
    specialize (H0 H2); clear H2.
    omega.
  }
  (* Theta2O *)
  {
    exists a1, a2, N.
    intros.
    split. omega.
    split. omega.
    split. omega.
    intros.
    specialize (H0 La st1 st2 t H H1).
    split. tauto.
    destruct H0 as [_ ?].
    simpl in *. intros.
    specialize (H0 H2); clear H2.
    omega.
  }
  (* HighestEquivTheta *)
  {
    (* TODO: Fill in here *)
    admit.
  }
Admitted.

Lemma hoare_while_linear_sound : forall P (b : bexp) (V : term) (n m : logical_var) (C : term) c p,
  |== {{ P AND {[b]} AND V==n }} c {{P AND V==n-C}} $ BigO p n ->
  |== {{P AND V==m }} While b Do c EndWhile {{ P AND NOT {[b]} AND V==0 }} $ BigO (LINEAR *** p) m.
Proof.
(* TODO: Fill in here *)
Admitted.

Theorem hoare_logic_sound (F: FirstOrderLogic) : forall P Q c T,
  |-- {{P}} c {{Q}} $ T ->
  |== {{P}} c {{Q}} $ T.
Proof.
(* TODO: Fill in here *)
Admitted.
(** [] *)
