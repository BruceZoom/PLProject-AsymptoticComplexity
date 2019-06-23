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

Print aexp.
Print term.
Print bexp.
Print Assertion.

Lemma nat_plus_eqO : forall (x y : nat),
  plus x y = 0%nat ->
  x = 0%nat /\ y = 0%nat.
Proof.
  intros.
  destruct x, y; auto; try inversion H.
Qed.

Lemma update_lassn_diff : forall La x y z,
  x <> y ->
  La x = (Lassn_update La y z) x.
Proof.
  intros.
  unfold Lassn_update.
  destruct (Nat.eq_dec y x); [congruence | auto].
Qed.

Lemma update_lassn_sep_term : forall La st V n z,
  term_occur n V = O ->
  term_denote (st, La) V = term_denote (st, (Lassn_update La n z)) V.
Proof.
  intros.
  induction V; intros; auto; try inversion H.
  - destruct (Nat.eq_dec n x).
    + congruence.
    + simpl. apply update_lassn_diff. auto.
  - simpl.
    admit.
  - simpl.
    apply nat_plus_eqO in H1.
    destruct H1.
    rewrite (IHV1 H0).
    rewrite (IHV2 H1).
    reflexivity.
  - simpl.
    apply nat_plus_eqO in H1.
    destruct H1.
    rewrite (IHV1 H0).
    rewrite (IHV2 H1).
    reflexivity.
  - simpl.
    apply nat_plus_eqO in H1.
    destruct H1.
    rewrite (IHV1 H0).
    rewrite (IHV2 H1).
    reflexivity.
  Admitted.

Lemma update_lassn_sep_aexp : forall La st a n z,
  aexp_occur n a = O ->
  aexp'_denote (st, La) a = aexp'_denote (st, (Lassn_update La n z)) a.
Proof.
  intros.
  induction a; auto; try inversion H.
  - induction t.
    + simpl. reflexivity.
    + simpl in *. unfold Lassn_update.
      destruct (Nat.eq_dec n x); [congruence | auto].
    + simpl in *.
    Admitted.

Lemma update_lassn_sep_bexp : forall La st b n z,
  bexp_occur n b = O ->
  bexp'_denote (st, La) b = bexp'_denote (st, (Lassn_update La n z)) b.
Proof.
  intros.
  induction b; auto.
  - simpl. inversion H.
  Admitted.

Lemma update_lassn_sep_assn : forall La st n z P,
  assn_occur n P = O ->
  (st, La) |== P <-> (st, (Lassn_update La n z)) |== P.
Proof.
  intros.
  Admitted.

Lemma hoare_while_linear_sound : forall (T: FirstOrderLogic) P (b : bexp) (V : term) (m : logical_var) (n : logical_var) (C : Z) c p,
  {[b]} |-- 0 <= V ->
  assn_occur n P = O ->
  term_occur n V = O ->
  bexp_occur n b = O ->
  |== {{P AND {[b]} AND V == n}} c {{P AND V == n-1}} $ BigO p n ->
  |== {{P AND V == n }} While b Do c EndWhile {{ P AND NOT {[b]} }} $ BigO (LINEAR *** p) n.
Proof.
  intros.
  rename H0 into Hao.
  rename H1 into Hto.
  rename H2 into Hbo.
  rename H3 into H0.
  unfold valid in *.
  destruct H0 as [a1 [a2 [N [h1 [h2 [h3 ?]]]]]].
  simpl in H0.
  exists a1, a2, N.
  
  split; auto.
  split; auto.
  split; auto.
  
  intros.
  simpl in H1, H2.
  destruct H1 as [? ?].
  unfold loop_sem in H2.
  destruct H2 as [n' ?].
  
  generalize dependent st1.
  revert La t.
(*  generalize dependent m.*)
  induction n'; intros.
  - simpl in H2.
    destruct H2 as [[? ?] ?].
    split.
    + simpl.
      subst st2 t.
      pose proof beval_bexp'_denote st1 La b.
      tauto.
    + subst st2 t.
      unfold ab_eval.
      intros. admit. (* We have a problem here! Nothing specify any property about p. *)
  - simpl in H2.
    destruct H2 as [[t1 [t2 [st3 [? [? ?]]]]] ?].
    pose proof beval_bexp'_denote st1 La b.
    assert ((((st1, La) |== P) /\ bexp'_denote (st1, La) b) /\ term_denote (st1, La) V = La n). tauto.
    (*pose proof H0 La st1 st3 t1 H8 H2.*)
    pose proof H0 La st1 st3 t1 H8 H2; clear H8.
    destruct H9 as [[? ?] ?].
    
    assert (Lassn_update La n (La n - 1) n = La n - 1) as Hupn.
    {
      unfold Lassn_update.
      destruct (Nat.eq_dec n n); [auto | congruence].
    }
    
    assert (term_denote (st3, Lassn_update La n (La n - 1)) V = Lassn_update La n (La n - 1) n).
    {
      pose proof update_lassn_sep_term La st3 V n (La n - 1) Hto.
      rewrite <- H11. rewrite H9.
      rewrite Hupn. reflexivity.
    }
    assert ((st3, Lassn_update La n (La n - 1)) |== P).
    {
      pose proof update_lassn_sep_assn La st3 n (La n - 1) P Hao.
      rewrite H12 in H8.
      exact H8.
    }
    pose proof IHn' (Lassn_update La n (La n - 1)) t2 st3 H12 H11 H4; clear H11 H12.
    destruct H13.
    split.
    + destruct H11.
      pose proof update_lassn_sep_assn La st2 n (La n - 1) P Hao.
      rewrite <- H14 in H11; clear H14.
      pose proof update_lassn_sep_assn La st2 n (La n - 1) (NOT {[b]}).
      split. exact H11.
      rewrite H14. exact H13.
      simpl. exact Hbo.
    + clear H1 H3 H2 H4 H6 H7 H8 H9 H11.
      unfold ab_eval in H12.
      unfold ab_eval. rewrite Hupn in *.
      intros.
      
      assert (N <= La n - 1). admit.
      specialize (H10 H1); clear H1.
      specialize (H12 H2); clear H2.
      rewrite H5.
      
      split.
      omega.
      rewrite poly_mult_spec, LINEAR_spec in H12.
      rewrite poly_mult_spec, LINEAR_spec.
Admitted.

Theorem hoare_logic_sound (F: FirstOrderLogic) : forall P Q c T,
  |-- {{P}} c {{Q}} $ T ->
  |== {{P}} c {{Q}} $ T.
Proof.
(* TODO: Fill in here *)
Admitted.
(** [] *)
