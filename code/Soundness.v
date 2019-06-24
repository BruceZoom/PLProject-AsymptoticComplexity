Require Import AB.Imp9.
Require Import AB.Denotation.
Require Import AB.HoareLogic.
Require Import Coq.Lists.List.

Open Scope list_scope.

Import Assertion_D.
Export Abstract_Pretty_Printing.

Import Command_Denotation_With_Steps.
Import Hoare_Logic.

Definition valid (Tr: hoare_triple): Prop :=
  match Tr with
  | Build_hoare_triple P c Q T =>
      exists a1 a2, 0 < a1 /\ 0 < a2 /\
      forall La st1 st2 t,
        (st1, La) |== P ->
        ceval c st1 t st2 ->
        ((st2, La) |== Q) /\ ab_eval La T a1 a2 t
  end.

Notation "|==  Tr" := (valid Tr) (at level 91, no associativity).

(** Soundness Proof *)

Lemma hoare_skip_sound : forall P n,
  |== {{P}} Skip {{P}} $ BigTheta CONSTANT n.
Proof.
  unfold valid.
  exists 1, 1.
  
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
Admitted.

Lemma hoare_asgn_bwd_sound : forall P (X: var) (E: aexp) n,
  |== {{ P [ X |-> E] }} X ::= E {{ P }} $ BigTheta CONSTANT n.
Proof.
  unfold valid.
  exists 1, 1.
  
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
  destruct H as [a1 [a2 [h1 [h2 ?]]]].
  destruct H0 as [a1' [a2' [h1' [h2' ?]]]].
  simpl in *.
  exists (Z.min a1 a1'), (Z.max a2 a2').
  
  split. apply (Z.min_glb_lt _ _ _ h1 h1').
  split. pose proof Z.le_max_l a2 a2'. omega.
  
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
    (*
    pose proof Z.max_lub_l _ _ _ H7;
    pose proof Z.max_lub_r _ _ _ H7;
    clear H7.
    specialize (H5 H8); clear H8.
    specialize (H6 H9); clear H9.
    *)
    specialize (H5 H7);
    specialize (H6 H7);
    clear H7.
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
  destruct H as [a1 [a2 [h1 [h2 ?]]]].
  destruct H0 as [a1' [a2' [h1' [h2' ?]]]].
  simpl in *.
  exists (Z.min a1 a1'), (2 * (Z.max a2 a2')).
  
  split. apply (Z.min_glb_lt _ _ _ h1 h1').
  split. pose proof Z.le_max_l a2 a2'. omega.
  
  intros.
  unfold if_sem in H2.
  destruct H2 as [[? ?] | [? ?]].
  - (* if branch *)
    pose proof beval_bexp'_denote st1 La b.
    pose proof H La st1 st2 t.
    split.
    {
      tauto.
    }
    {
      assert (ab_eval La T a1 a2 t) as HAB. tauto.
(*      pose proof command_cost_time _ _ _ _ H2 as HT.*)
      clear H H0 H1 H2 H3 H4 H5.
      destruct T;
      unfold ab_eval in *;
      intros;
      remember (poly_eval p (La l)) as T.
      - (* BigO *)
        pose proof HAB H as [? ?].
        assert (0 <= a2 * T). omega.
        rewrite (Z.mul_nonneg_cancel_l _ _ h2) in H2.
        rewrite <- Z.mul_assoc.
        rewrite <- (Z.mul_max_distr_nonneg_r _ _ _ H2).
        pose proof Z.le_max_l (a2 * T) (a2' * T).
        omega.
      - (* BigOmega *)
        pose proof HAB H as [? ?].
        pose proof H0.
        rewrite (Z.mul_nonneg_cancel_l _ _ h1) in H2.
        rewrite <- (Z.mul_min_distr_nonneg_r _ _ _ H2).
        pose proof Z.le_min_l (a1 * T) (a1' * T).
        assert (0 <= a1' * T). apply Z.mul_nonneg_nonneg; omega.
        pose proof Z.min_glb _ _ _ H0 H4.
        omega.
      - (* BigTheta *)
        pose proof HAB H as [[? ?] ?].
        pose proof H0.
        rewrite (Z.mul_nonneg_cancel_l _ _ h1) in H3.
        rewrite <- (Z.mul_min_distr_nonneg_r _ _ _ H3).
        rewrite <- Z.mul_assoc.
        rewrite <- (Z.mul_max_distr_nonneg_r _ _ _ H3).
        assert (0 <= a1' * T). apply Z.mul_nonneg_nonneg; omega.
        assert (0 <= a1 * T). apply Z.mul_nonneg_nonneg; omega.
        clear H3.
        split.
        + pose proof Z.le_min_l (a1 * T) (a1' * T).
          pose proof Z.min_glb _ _ _ H5 H4.
          omega.
        + pose proof Z.le_max_l (a2 * T) (a2' * T).
(*
          assert (t <= 2 * t - 2).
          {
            rewrite <- Z.add_diag.
            rewrite <- Z.add_sub_assoc.
            rewrite <- Z.add_0_r at 1.
            apply Zplus_le_compat_l.
            omega.
          }
*)
          omega.
    }
  - (* else branch *)
    pose proof beval_bexp'_denote st1 La b.
    pose proof H0 La st1 st2 t.
    split.
    {
      tauto.
    }
    {
      assert (ab_eval La T a1' a2' t) as HAB. tauto.
(*      pose proof command_cost_time _ _ _ _ H2 as HT.*)
      clear H H0 H1 H2 H3 H4 H5.
      destruct T;
      unfold ab_eval in *;
      intros;
      remember (poly_eval p (La l)) as T.
      - (* BigO *)
        pose proof HAB H as [? ?].
        assert (0 <= a2' * T). omega.
        rewrite (Z.mul_nonneg_cancel_l _ _ h2') in H2.
        rewrite <- Z.mul_assoc.
        rewrite <- (Z.mul_max_distr_nonneg_r _ _ _ H2).
        pose proof Z.le_max_r (a2 * T) (a2' * T).
        omega.
      - (* BigOmega *)
        pose proof HAB H as [? ?].
        pose proof H0.
        rewrite (Z.mul_nonneg_cancel_l _ _ h1') in H2.
        rewrite <- (Z.mul_min_distr_nonneg_r _ _ _ H2).
        pose proof Z.le_min_r (a1 * T) (a1' * T).
        assert (0 <= a1 * T). apply Z.mul_nonneg_nonneg; omega.
        pose proof Z.min_glb _ _ _ H4 H0.
        omega.
      - (* BigTheta *)
        pose proof HAB H as [[? ?] ?].
        pose proof H0.
        rewrite (Z.mul_nonneg_cancel_l _ _ h1') in H3.
        rewrite <- (Z.mul_min_distr_nonneg_r _ _ _ H3).
        rewrite <- Z.mul_assoc.
        rewrite <- (Z.mul_max_distr_nonneg_r _ _ _ H3).
        assert (0 <= a1' * T). apply Z.mul_nonneg_nonneg; omega.
        assert (0 <= a1 * T). apply Z.mul_nonneg_nonneg; omega.
        clear H3.
        split.
        + pose proof Z.le_min_r (a1 * T) (a1' * T).
          pose proof Z.min_glb _ _ _ H5 H4.
          omega.
        + pose proof Z.le_max_r (a2 * T) (a2' * T).
(*
          assert (t <= 2 * t - 2).
          {
            rewrite <- Z.add_diag.
            rewrite <- Z.add_sub_assoc.
            rewrite <- Z.add_0_r at 1.
            apply Zplus_le_compat_l.
            omega.
          }
*)
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
  destruct H0 as [a1 [a2 [h1 [h2 ?]]]].
(*  pose proof loosen_valid _ _ H as Hlv.*)
  induction H.
  (* Theta2Omega *)
  {
    exists a1, a2.
    intros.
    split. omega.
    split. omega.
    intros.
    specialize (H0 La st1 st2 t H1 H2).
    split. tauto.
    destruct H0 as [_ ?].
    simpl in *. intros.
    specialize (H0 H3); clear H2.
    omega.
  }
  (* Theta2O *)
  {
    exists a1, a2.
    intros.
    split. omega.
    split. omega.
    intros.
    specialize (H0 La st1 st2 t H1 H2).
    split. tauto.
    destruct H0 as [_ ?].
    simpl in *. intros.
    specialize (H0 H3); clear H2.
    omega.
  }
  (* O_Poly2Mono *)
  {
    (* TODO: Fill in here *)
    exists a1.
    exists ((poly_get_max p 0)*(Z.of_nat (length p))*a2).
    assert (forall (N:nat) (z:Z), (Datatypes.length (repeat z N)) = N) as lem_repeat.
    { intros. simpl.
      induction N.
      - simpl. reflexivity.
      - simpl. rewrite IHN. reflexivity.
    }
    assert (length p <> 0)%nat as p_gt0.
    { unfold not. intros.
      apply length_zero_iff_nil in H1.
      subst. simpl in H. 
      omega.
    }
    assert (p <> nil) as p_nnil.
    { unfold not. intros.
      subst. simpl in H.
      omega.
    }
    assert (poly_get_max p 0 > 0).
    { pose proof poly_get_max3 p (poly_get_last p).
      destruct p.
      - simpl in H. omega.
      - remember (z::p) as l.
        pose proof poly_get_last_in_poly l.
        pose proof H2 p_nnil.
        pose proof H1 H3.
        pose proof Z.lt_le_trans _ _ _ H H4.
        omega.
    }
    split. omega.
    split. assert (a2 > 0) as h2'. { omega. }
    assert (Z.of_nat (length p)> 0).
    { pose proof Nat2Z.is_nonneg (length p).

      omega.
    }
    pose proof Zmult_gt_0_compat _ _ H1 H2.
    pose proof Zmult_gt_0_compat _ _ H3 h2'.
    apply Z.gt_lt in H4.
    exact H4.

    intros.
    specialize (H0 La st1 st2 t H2 H3). destruct H0.
    split.
    - tauto.
    - simpl. intros. 
      simpl in H4. pose proof H4 H5.
      assert (a2 * poly_eval p (La n) <= poly_get_max p 0 * (Z.of_nat (Datatypes.length p)) * a2 * poly_eval (poly_monomialize p) (La n)).
      { pose proof poly_eval_mono p (La n).
        rewrite H7.
        pose proof poly_distr_coef_compare (poly_get_max p 0) (Datatypes.length p) (La n).
        pose proof Z.lt_gt _ _ H5 as H5'.
        pose proof H8 H1 H5'.
        clear H8.
        pose proof poly_eval_app (repeat 0 (Z.to_nat (Z.of_nat (Datatypes.length p) - 1))) (poly_get_max p 0 * Z.of_nat (Datatypes.length p) :: nil) (La n).
        pose proof poly_eval_zero (Z.to_nat (Z.of_nat (Datatypes.length p) - 1)) (La n).
        rewrite H10 in H8. clear H10. 
        rewrite H8 in H9. clear H8.
        rewrite Z.add_0_l in H9.
       
        pose proof lem_repeat (Z.to_nat (Z.of_nat (Datatypes.length p) - 1)).
        rewrite H8 in H9. clear H8.
        pose proof Z2Nat.id (Z.of_nat (Datatypes.length p) - 1).
        assert (0 <= Z.of_nat (Datatypes.length p) - 1).
        { omega. }
        pose proof H8 H10. clear H8 H10.
        rewrite H11 in H9. clear H11.
        assert (poly_eval (poly_get_max p 0 * Z.of_nat (Datatypes.length p) :: nil) (La n) = poly_get_max p 0 * Z.of_nat (Datatypes.length p)).
        { simpl. omega. }
        rewrite H8 in H9. clear H8.
        apply Z.ge_le in H9.
        rewrite Z.mul_comm in H9.
        rename H9 into FirstPart.
        
        assert (term_by_term_le p (repeat (poly_get_max p 0) (Datatypes.length p))).
        { unfold term_by_term_le.
          clear H H0 H1 H2 H3 H4 H5 H5' H6 H7 p_gt0 p_nnil FirstPart.
          induction p.
          - simpl. apply nil_le.
          - assert (length p = length (repeat (poly_get_max p 0) (Datatypes.length p))).
            { pose proof lem_repeat (Datatypes.length p) (poly_get_max p 0).
              rewrite H.
              omega.
            }
            admit.
         }
         pose proof poly_each_coef_compare p (repeat (poly_get_max p 0) (Datatypes.length p)).
         pose proof lem_repeat (Datatypes.length p) (poly_get_max p 0).
         apply eq_sym in H10.
         pose proof H9 H10. clear H9 H10.
         pose proof H11 H8. clear H11 H8.
         specialize (H9 (La n)).
         assert (0 <= La n). omega.
         pose proof H9 H8. clear H9 H8.
         rename H10 into SecondPart.
         
         pose proof Z.le_trans _ _ _ SecondPart FirstPart.
         rename H8 into ThirdPart.
         
         assert (a2 <= a2 * (poly_get_last p)) as FourthPart.
         { assert (1 <= poly_get_last p). omega.
           pose proof Z.mul_le_mono_nonneg 1 (poly_get_last p) a2 a2.
           assert (0 <= 1). omega.
           assert (0 <= a2). omega.
           assert (a2 <= a2). omega.
           pose proof H9 H10 H8 H11 H12.
           rewrite Z.mul_1_l in H13.
           rewrite Z.mul_comm in H13.
           exact H13.
         }
         pose proof Z.mul_le_mono_nonneg a2 (a2 * (poly_get_last p)) (poly_eval p (La n)) (poly_get_max p 0 * Z.of_nat (Datatypes.length p) * La n ^ (Z.of_nat (Datatypes.length p) - 1)).
         assert (0 <= a2). omega.
         pose proof H8 H9 FourthPart.
         assert (0 <= poly_eval p (La n)).
         { pose proof Zmult_le_0_reg_r a2 (poly_eval p (La n)).
           assert (a2 > 0). omega.
           pose proof H11 H12.
           rewrite Z.mul_comm in H13.
           assert (0 <= a2 * poly_eval p (La n)). omega.
           pose proof H13 H14.
           exact H15.
         }
         pose proof H10 H11.
         pose proof H12 ThirdPart.
         assert (a2 * poly_get_last p * (poly_get_max p 0 * Z.of_nat (Datatypes.length p) * La n ^ (Z.of_nat (Datatypes.length p) - 1)) = poly_get_max p 0 * Z.of_nat (Datatypes.length p) * a2 * (poly_get_last p * La n ^ (Z.of_nat (Datatypes.length p) - 1))).
         ring.
         rewrite H14 in H13. clear H14.
         rename H13 into final.
         exact final.
      }
      omega.
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
  term_denote (st, La) V = term_denote (st, (Lassn_update La n z)) V
  with update_lassn_sep_aexp : forall La st a n z,
  aexp_occur n a = O ->
  aexp'_denote (st, La) a = aexp'_denote (st, (Lassn_update La n z)) a.
Proof.
{
  intros.
  clear update_lassn_sep_term.
  induction V; intros; auto; try inversion H.
  - destruct (Nat.eq_dec n x).
    + congruence.
    + simpl. apply update_lassn_diff. auto.
  - simpl.
    rewrite <- update_lassn_sep_aexp; auto.
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
}
{
  intros.
  clear update_lassn_sep_aexp.
  induction a; intros; auto; try inversion H.
  - simpl.
    rewrite <- update_lassn_sep_term; auto.
  - simpl.
    apply nat_plus_eqO in H1 as [? ?].
    rewrite (IHa1 H0), (IHa2 H1).
    reflexivity.
  - simpl.
    apply nat_plus_eqO in H1 as [? ?].
    rewrite (IHa1 H0), (IHa2 H1).
    reflexivity.
  - simpl.
    apply nat_plus_eqO in H1 as [? ?].
    rewrite (IHa1 H0), (IHa2 H1).
    reflexivity.
}
Qed.

Lemma update_lassn_sep_bexp : forall La st b n z,
  bexp_occur n b = O ->
  bexp'_denote (st, La) b = bexp'_denote (st, (Lassn_update La n z)) b.
Proof.
  intros.
  induction b; auto; inversion H.
  - simpl. apply nat_plus_eqO in H1 as [? ?].
    rewrite <- (update_lassn_sep_aexp _ _ _ _ _ H0).
    rewrite <- (update_lassn_sep_aexp _ _ _ _ _ H1).
    reflexivity.
  - apply nat_plus_eqO in H1 as [? ?].
    simpl.
    rewrite <- (update_lassn_sep_aexp _ _ _ _ _ H0).
    rewrite <- (update_lassn_sep_aexp _ _ _ _ _ H1).
    reflexivity.
  - simpl. rewrite (IHb H1). reflexivity.
  - simpl. apply nat_plus_eqO in H1 as [? ?].
    rewrite (IHb1 H0), (IHb2 H1).
    reflexivity.
Qed.

Lemma update_lassn_sep_assn : forall La st n z P,
  assn_occur n P = O ->
  (st, La) |== P <-> (st, (Lassn_update La n z)) |== P.
Proof.
  intros. revert La.
  induction P; simpl; try inversion H; split; intros;
    try (apply nat_plus_eqO in H1 as [? ?]);
    try (rewrite <- (update_lassn_sep_term _ _ _ _ _ H1);
      rewrite <- (update_lassn_sep_term _ _ _ _ _ H2);
      assumption);
    try (erewrite (update_lassn_sep_term _ _ _ _ _ H1);
      erewrite (update_lassn_sep_term _ _ _ _ _ H2);
      apply H0);
    try (rewrite (IHP1 H1), (IHP2 H2); assumption);
    try (rewrite <- (IHP1 H1); rewrite <- (IHP2 H2); assumption);
    try (destruct H0; [left; apply IHP1 | right; apply IHP2];
      assumption);
    try (destruct H0; split;
      [apply IHP1 | apply IHP2];
      assumption);
    try (destruct (Nat.eq_dec n x); [inversion H1 |];
      destruct H0 as [v ?];
      exists v).
    - rewrite <- (update_lassn_sep_bexp _ _ _ _ _ H1).
      assumption.
    - erewrite (update_lassn_sep_bexp _ _ _ _ _ H1).
      apply H0.
    - rewrite <- (IHP H1); assumption.
    - rewrite (IHP H1); assumption.
    - unfold Interp_Lupdate in *. simpl in *.
      rewrite (IHP H1) in H0.
      pose proof Lassn_update_update_diff st La n x z v n0.
      rewrite (satisfies_Interp_Equiv _ _ _ H2).
      exact H0.
    - unfold Interp_Lupdate in *. simpl in *.
      rewrite (IHP H1).
      pose proof Lassn_update_update_diff st La n x z v n0.
      rewrite <- (satisfies_Interp_Equiv _ _ _ H2).
      exact H0.
    - destruct (Nat.eq_dec n x); [inversion H1 |].
      unfold Interp_Lupdate in *. simpl in *.
      specialize (H0 v).
      rewrite (IHP H1) in H0.
      pose proof Lassn_update_update_diff st La n x z v n0.
      rewrite (satisfies_Interp_Equiv _ _ _ H2).
      exact H0.
    - destruct (Nat.eq_dec n x); [inversion H1 |].
      unfold Interp_Lupdate in *. simpl in *.
      specialize (H0 v).
      rewrite (IHP H1).
      pose proof Lassn_update_update_diff st La n x z v n0.
      rewrite <- (satisfies_Interp_Equiv _ _ _ H2).
      exact H0.
Qed.

Lemma hoare_while_linear_sound : forall (T: FirstOrderLogic) P (b : bexp) (V : term) (n : logical_var) (C : Z) c p,
  (forall st La, ((st, La) |== (P AND {[b]})) -> ((st, La) |== (0 < V))) ->
  assn_occur n P = O ->
  term_occur n V = O ->
  bexp_occur n b = O ->
  (forall x, 0 < x -> 0 <= poly_eval p x) ->
  (forall x y, x <= y -> poly_eval p x <= poly_eval p y) ->
  |== {{P AND {[b]} AND V == n}} c {{P AND V == n-1}} $ BigO p n ->
  |== {{P AND V == n }} While b Do c EndWhile {{ P AND NOT {[b]} }} $ BigO (LINEAR *** p) n.
Proof.
  intros.
  rename H0 into Hao.
  rename H1 into Hto.
  rename H2 into Hbo.
  rename H3 into Hpre.
  rename H4 into Hinc.
  rename H5 into H0.
  unfold valid in *.
  destruct H0 as [a1 [a2 [h1 [h2 ?]]]].
  simpl in H0.
  exists a1, a2.
  
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
      intros.
      rewrite poly_mult_spec, LINEAR_spec.
      pose proof Hpre _ H2.
      split; [omega |].
      apply Z.mul_nonneg_nonneg; [omega |].
      apply Z.mul_nonneg_nonneg; omega.
  - simpl in H2.
    destruct H2 as [[t1 [t2 [st3 [? [? ?]]]]] ?].

    assert (0 < La n) as Hn.
    {
      pose proof H st1 La.
      simpl in H7.
      rewrite H3 in H7.
      apply H7.
      pose proof beval_bexp'_denote st1 La b.
      tauto.
    }

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
    + pose proof excluded_middle (La n = 1).
      destruct H13.
      {
        clear H1 H3 H2 H4 H6 H7 H8 H9 H11.
        unfold ab_eval in H12.
        unfold ab_eval. rewrite Hupn in *.
        intros.
        
        specialize (H10 H1); clear H1.
        assert (0 < La n - 1). omega.
        specialize (H12 H1); clear H1.
        rewrite H5.
        
        split; [omega |].
        rewrite poly_mult_spec, LINEAR_spec in H12.
        rewrite poly_mult_spec, LINEAR_spec.
        assert ((La n - 1) <= (La n)). omega.
        pose proof Hinc (La n - 1) (La n) H1.
        assert (t2 <= a2 * ((La n - 1) * poly_eval p (La n))).
        {
          assert ((La n - 1) * poly_eval p (La n - 1) <= (La n - 1) * poly_eval p (La n)).
          {
            assert (0 <= La n - 1). omega.
            apply Z.mul_le_mono_nonneg_l.
            exact H3. exact H2.
          }
          eapply Z.le_trans.
          2:{
            apply Z.mul_le_mono_nonneg_l. omega.
            apply H3.
          }
          omega.
        }
        destruct H10.
        pose proof Z.add_le_mono _ _ _ _ H6 H3.
        rewrite Z.mul_assoc.
        rewrite Z.mul_assoc in H7.
        assert (La n = 1 + (La n - 1)). omega.
        rewrite H8 at 1; clear H8.
        rewrite Z.mul_add_distr_l.
        rewrite Z.mul_add_distr_r.
        rewrite Z.mul_1_r.
        exact H7.
      }
      {
        rewrite H13 in *; clear H13.
        destruct n'.
        + destruct H4 as [[? ?] ?].
          subst. unfold ab_eval; intros.
          specialize (H10 Hn).
          rewrite poly_mult_spec, LINEAR_spec.
          assert (poly_eval p 1 <= La n * poly_eval p (La n)).
          {
            assert (1 <= La n). omega.
            assert (poly_eval p 1 = 1 * poly_eval p 1). ring.
            rewrite H13; clear H13.
            apply Z.mul_le_mono_nonneg; try omega.
            apply Hpre. omega.
            apply Hinc. auto.
          }
          apply (Z.mul_le_mono_nonneg_l (poly_eval p 1) (La n * poly_eval p (La n)) a2) in H5; omega.
        + destruct H4 as [? ?].
          rewrite (beval_bexp'_denote st3 La b) in H13.
          assert ((st3, La) |== P AND {[b]}). simpl. tauto.
          pose proof H _ _ H14; clear H14.
          simpl in H15. rewrite H9 in H15.
          inversion H15.
      }
Qed.

Definition FOL_valid {T: FirstOrderLogic} (P: Assertion): Prop :=
  forall J: Interp, J |== P.

Definition FOL_sound (T: FirstOrderLogic): Prop :=
  forall P: Assertion, FOL_provable P -> FOL_valid P.

Theorem hoare_consequence_sound (F: FirstOrderLogic) : forall (P P' Q Q' : Assertion) c (T : AsymptoticBound),
      FOL_sound F ->
      P |-- P' ->
      |== {{P'}} c {{Q'}} $ T ->
      Q' |-- Q ->
      |== {{P}} c {{Q}} $ T.
Proof.
  intros.
  unfold FOL_sound in H.
  unfold derives in H0, H2.
  apply H in H0.
  apply H in H2.
  unfold FOL_valid in H0, H2.
  simpl in H0, H2.
  unfold valid in H1.
  unfold valid.
  
  destruct H1 as [a1 [a2 [h1 [h2 ?]]]].
  exists a1, a2.
  split; auto.
  split; auto.
  
  intros.
  assert ((st1, La) |== P').
  {
    specialize (H0 (st1, La)).
    tauto.
  }
  pose proof H1 _ _ _ t H5 H4.
  specialize (H2 (st2, La)).
  tauto.
Qed.

Theorem hoare_logic_sound (F: FirstOrderLogic) : forall P Q c T,
  |-- {{P}} c {{Q}} $ T ->
  |== {{P}} c {{Q}} $ T.
Proof.
(* TODO: Fill in here *)
Admitted.
(** [] *)
