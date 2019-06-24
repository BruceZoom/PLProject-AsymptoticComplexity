Require Import AB.Imp8.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Open Scope Z.

Module Polynomial.
Import Assertion_D.

(** Definitions of poly *)
Definition poly := list Z. (* The power increases as the index goes up *)

Definition ZERO : poly := nil.
Definition CONSTANT : poly := 1::nil.
Definition LINEAR : poly := 0::1::nil.
Definition QUADRATIC : poly := 0::0::1::nil.
Definition CUBIC : poly := 0::0::0::1::nil.
(** [] *)

(** Evaluations of polynomial *)
Fixpoint poly_eval (p : poly) : Z -> Z := 
  fun z => 
    match p with
    | nil => 0
    | h :: t => h + z * (poly_eval t z)
    end.

Open Scope term_scope.
Print aexp'.

Fixpoint TPower (v : logical_var) (n : nat) : term :=
  match n with
  | O => 1
  | S n' => v * (TPower v n')
  end.

Fixpoint poly_eval_lv (p : poly) : logical_var -> term :=
  fun v =>
    match p with
    | nil => 0
    | h :: t => h + v * (poly_eval_lv t v)
    end.

Close Scope term_scope.
(** [] *)

(** Operations of polynomial *)
Fixpoint poly_add (p1 p2 : poly) : poly :=
  match p1, p2 with
  | nil, nil => nil
  | h::t, nil => h::t
  | nil, h::t => h::t
  | h::t, h'::t' => (h+h')::(poly_add t t')
  end.

Fixpoint trim_0 (p : poly) : poly :=
  match p with
  | nil => nil
  | h :: t => match trim_0 t with
              | nil => if Z.eq_dec h 0 then nil else h :: nil
              | _ => h :: trim_0 t
              end
  end.

Fixpoint poly_scalar_mult (k : Z) (p : poly) : poly :=
  match p with
  | nil => nil
  | h :: t => k * h :: poly_scalar_mult k t
  end.

Fixpoint poly_mult (p1 p2 : poly) : poly := 
  match p1, p2 with
  | nil, _ => nil
  | _, nil => nil
  | h :: t, _ => poly_add (poly_scalar_mult h p2) (0 :: (poly_mult t p2))
  end.

Notation "p '+++' q" := (poly_add p q) (at level 60).
Notation "k ** p" := (poly_scalar_mult k p) (at level 60).
Notation "p '***' q" := (poly_mult p q) (at level 60).

Section Examples.

Example poly_add_eg : poly_eval ((CONSTANT +++ LINEAR) +++ (CONSTANT +++ QUADRATIC)) 2 = 8.
Proof.
  simpl. reflexivity.
Qed.

Example poly_mult_eg : poly_eval ((CONSTANT +++ LINEAR) *** (CONSTANT +++ QUADRATIC)) 2 = 15.
Proof.
  simpl. reflexivity.
Qed.

End Examples.
(** [] *)

(** Properties of Shorthand Notations *)
Fact CONSTANT_spec : forall z, poly_eval CONSTANT z = 1.
Proof.
  intros.
  simpl.
  rewrite Z.mul_0_r.
  reflexivity.
Qed.

Fact LINEAR_spec : forall z, poly_eval LINEAR z = z.
Proof.
  intros.
  simpl.
  rewrite Z.mul_0_r.
  omega.
Qed.

Fact QUADRATIC_spec : forall z, poly_eval QUADRATIC z = z*z.
Proof.
  intros.
  simpl.
  rewrite Z.mul_0_r.
  ring.
Qed.

Fact CUBIC_spec : forall z, poly_eval CUBIC z = z*z*z.
Proof.
  intros.
  simpl.
  rewrite Z.mul_0_r.
  ring.
Qed.
(** [] *)

(** Properties of Polynomial Operations *)
Lemma poly_add_nil_l : forall p, poly_add nil p = p.
Proof.
  intros.
  destruct p.
  - auto.
  - simpl. reflexivity.
Qed.

Lemma poly_add_nil_r : forall p, poly_add p nil = p.
Proof.
  intros.
  destruct p.
  - auto.
  - simpl. reflexivity.
Qed.

Lemma poly_mult_nil_l : forall p, poly_mult nil p = nil.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma poly_mult_nil_r : forall p, poly_mult p nil = nil.
Proof.
  intros.
  destruct p; auto.
Qed.

Lemma poly_eval_zero: forall n z,
  poly_eval (repeat 0 n) z = 0.
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. omega.
Qed.

Theorem poly_add_spec : forall (p1 p2 : poly) (z : Z),
  poly_eval (poly_add p1 p2) z = poly_eval p1 z + poly_eval p2 z.
Proof.
  intro.
  induction p1; intros.
  - rewrite poly_add_nil_l. simpl. reflexivity.
  - destruct p2.
    + simpl. omega.
    + simpl. rewrite IHp1.
      rewrite Z.mul_add_distr_l. omega.
Qed.

Theorem poly_scalar_mult_spec : forall (k : Z) (p : poly) (z : Z),
  poly_eval (poly_scalar_mult k p) z = k * poly_eval p z.
Proof.
  intros.
  induction p.
  - simpl. rewrite Z.mul_0_r. reflexivity.
  - simpl. rewrite IHp. ring.
Qed.

Theorem poly_mult_spec : forall (p1 p2 : poly) (z : Z),
  poly_eval (poly_mult p1 p2) z = poly_eval p1 z * poly_eval p2 z.
Proof.
  intro.
  induction p1; intros.
  - auto.
  - destruct p2.
    + simpl. rewrite Z.mul_0_r. reflexivity.
    + simpl.
      rewrite poly_add_spec. rewrite IHp1.
      rewrite poly_scalar_mult_spec. simpl.
      ring.
Qed.

Theorem trim_invar:
  forall p z,
  poly_eval (trim_0 p) z = poly_eval p z.
Proof.
  intro.
  induction p; intros.
  - auto.
  - simpl.
    destruct (trim_0 p) eqn:eqp.
    + destruct (Z.eq_dec a 0) eqn:eqa; rewrite <- IHp; simpl; omega.
    + rewrite <- eqp in *.
      simpl. rewrite IHp. reflexivity.
Qed.

Lemma poly_eval_cons : forall (p: poly) (a z : Z),
  poly_eval (a :: p) z = a + z * (poly_eval p z).
Proof.
  simpl.
  reflexivity.
Qed.

Lemma poly_eval_nil : forall (z : Z),
  poly_eval nil z = 0.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma poly_eval_app : forall (p1 p2 : poly) (z : Z),
  poly_eval (p1 ++ p2) z = poly_eval p1 z + (z^(Z.of_nat (length p1))) * (poly_eval p2 z).
Proof.
  intros. induction p1.
  - assert (Z.of_nat (Datatypes.length (nil:poly)) = 0). auto.
    rewrite app_nil_l.
    rewrite H. rewrite Z.pow_0_r.
    pose proof poly_eval_nil z. rewrite H0.
    omega.
  - rewrite <- app_comm_cons.
    pose proof poly_eval_cons (p1 ++ p2) a z.
    rewrite H. clear H. rewrite IHp1.
    rewrite Z.mul_add_distr_l.
    assert (z * (z ^ Z.of_nat (Datatypes.length p1)) = z ^ Z.of_nat (Datatypes.length (a :: p1))).
    {
      pose proof Z.pow_1_r z. rewrite <- H at 1.
      pose proof Z.pow_add_r z 1 (Z.of_nat (Datatypes.length p1)).
      assert (0 <= 1). omega.
      assert (0 <= Z.of_nat (Datatypes.length p1)). 
      {
        clear IHp1 H H0 H1.
        induction p1.
        - simpl. omega.
        - simpl. apply Zle_0_pos.
      }
      pose proof H0 H1 H2.
      rewrite <- H3.
      assert (1 + Z.of_nat (Datatypes.length p1) = Z.of_nat (Datatypes.length (a :: p1))).
      {
        clear IHp1 H H0 H1 H2 H3.
        pose proof Nat2Z.inj_add 1 (length p1).
        assert (Z.of_nat 1 = 1). auto.
        rewrite <- H0.
        rewrite <- H.
        pose proof inj_eq (1 + (length p1)) (length (a::p1)).
        assert ((1 + Datatypes.length p1)%nat = Datatypes.length (a :: p1)). auto.
        omega.
      }
      rewrite H4.
      omega.
    }
    rewrite <- H.
    pose proof poly_eval_cons p1 a z.
    rewrite H0.
    rewrite Z.mul_assoc.
    omega.
Qed.

Lemma poly_eval_add_zero_l: forall (p : poly) n z,
  poly_eval (poly_add (repeat 0 n) p) z = poly_eval p z.
Proof.
  intros.
  rewrite poly_add_spec.
  rewrite poly_eval_zero.
  omega.
Qed.

Lemma poly_eval_add_zero_r: forall (p : poly) n z,
  poly_eval (poly_add p (repeat 0 n)) z = poly_eval p z.
Proof.
  intros.
  rewrite poly_add_spec.
  rewrite poly_eval_zero.
  omega.
Qed.

Lemma poly_add_comm: forall p1 p2,
  poly_add p1 p2 = poly_add p2 p1.
Proof.
  intro.
  induction p1; intros.
  - rewrite poly_add_nil_l, poly_add_nil_r. reflexivity.
  - destruct p2.
    + auto.
    + simpl.
      rewrite IHp1.
      rewrite Z.add_comm.
      reflexivity.
Qed.
(** [] *)

(* Dealing with the coef *)
Fixpoint poly_coef_sum (p : poly) : Z :=
  match p with
  | nil => 0
  | h::t => h + (poly_coef_sum t)
  end.

End Polynomial.

Module Polynomial'.
Export Polynomial.
Import Assertion_D.

Definition poly' := list Z. (* The power decreases as the index goes up *)

(** Evaluations of polynomial' *)
Fixpoint poly'_eval (p : poly') : Z -> Z :=
  fun z =>
    match p with
    | nil => 0
    | h :: t => h * (Z.pow z (Z.of_nat (length t))) + (poly'_eval t z)
    end.

(** Operations of polynomial *)
Fixpoint poly'_add_body (l1 l2 : list Z) : list Z :=
  match l1, l2 with
  | nil, nil => l2
  | h::t, nil => h::t
  | nil, h::t => h::t
  | h::t, h'::t' => (h+h')::(poly'_add_body t t')
  end.

Definition poly'_add (p1 p2 : poly') : poly' := rev (poly'_add_body (rev p1) (rev p2)).

(** Properties of Polynomial Operations *)
Lemma poly'_add_body_empty_r : forall l, poly'_add_body l nil = l.
Proof.
  intros.
  destruct l.
  - auto.
  - simpl. reflexivity.
Qed.

Lemma poly'_add_empty_r : forall p, poly'_add p nil = p.
Proof.
  intros.
  destruct p.
  - auto.
  - unfold poly'_add.
    rewrite poly'_add_body_empty_r.
    apply rev_involutive.
Qed.

Lemma poly'_add_body_empty_l : forall l, poly'_add_body nil l = l.
Proof.
  intros.
  destruct l.
  - auto.
  - simpl. reflexivity.
Qed.

Lemma poly'_add_empty_l : forall p, poly'_add nil p = p.
Proof.
  intros.
  destruct p.
  - auto.
  - unfold poly'_add.
    rewrite poly'_add_body_empty_l.
    apply rev_involutive.
Qed.

Lemma poly'_eval_0s: forall times n,
  poly'_eval (repeat 0 times) n = 0.
Proof.
  intros.
  induction times.
  - simpl. reflexivity.
  - simpl. omega.
Qed.

Lemma poly'_cons_eval_comm : forall p z n,
  poly'_eval (cons z p) n = poly'_eval (cons z (repeat 0 (length p))) n + poly'_eval p n.
Proof.
  intros.
  simpl.
  assert (Datatypes.length (repeat 0 (Datatypes.length p)) = Datatypes.length p).
  { induction p.
    - simpl. reflexivity.
    - simpl. rewrite IHp. reflexivity.
  }
  rewrite H.
  pose proof poly'_eval_0s (Datatypes.length p) n.
  rewrite H0.
  omega.
Qed.

Lemma poly'_app_eval_comm: forall p1 p2 n,
  poly'_eval (p1 ++ p2) n = poly'_eval (p1 ++ (repeat 0 (length p2))) n + poly'_eval p2 n.
Proof.
  intros.
  induction p1.
  - simpl.
    pose proof app_nil_l p2.
    rewrite <- H. simpl.
    pose proof poly'_eval_0s (Datatypes.length p2) n.
    rewrite H0.
    omega.
  - pose proof poly'_cons_eval_comm.
    simpl.
    assert (Datatypes.length (p1 ++ repeat 0 (Datatypes.length p2)) = Datatypes.length (p1 ++ p2)).
    { clear IHp1 H.
      Search (length (_ ++ _)).
      assert (Datatypes.length (repeat 0%Z (Datatypes.length p2)) = Datatypes.length p2).
      { induction p2.
        - simpl. reflexivity.
        - simpl. rewrite IHp2. reflexivity.
      }
      pose proof app_length p1 p2.
      rewrite H0. 
      pose proof app_length p1 (repeat 0 (Datatypes.length p2)).
      rewrite H1.
      rewrite H.
      omega.
    }
    rewrite H0.
    rewrite IHp1.
    omega.
Qed.

Lemma poly'_eval_repeat_length_p: forall a (p : poly') z,
  poly'_eval (a :: repeat 0 (length p)) z = a * z ^ (Z.of_nat (length p)).
Proof.
  intros.
  simpl.
  pose proof poly'_eval_0s (length p) z.
  rewrite H.
  pose proof repeat_length 0 (length p).
  rewrite H0.
  omega.
Qed.

Theorem poly'_eval_poly_eval: forall (p : poly') n,
  poly'_eval p n = poly_eval (rev p) n.
Proof.
  intros.
  induction p.
  - simpl. reflexivity.
  - simpl. 
    pose proof poly_eval_app (rev p) (a::nil) n.
    rewrite H. simpl. clear H.
    rewrite IHp.
    pose proof rev_length p.
    rewrite H.
    assert (a + n * 0 = a). { omega. }
    rewrite H0.
    rewrite Z.mul_comm.
    omega.
Qed.

Theorem poly_eval_poly'_eval: forall (p : poly) n,
  poly_eval p n = poly'_eval (rev p) n.
Proof.
  intros.
  pose proof poly'_eval_poly_eval (rev p) n.
  rewrite rev_involutive in H.
  omega.
Qed.

End Polynomial'.

Module WZY_Poly_Enhance.
Export Polynomial.

Inductive list_le : poly -> poly -> Prop :=
  | nil_le : list_le nil nil
  | cons_le : forall p1 p2 a1 a2,
              length p1 = length p2 ->
              a1 <= a2 ->
              list_le p1 p2 ->
              list_le (a1 :: p1) (a2 :: p2).

End WZY_Poly_Enhance.

Module Monomial.
Export Polynomial.
Export Polynomial'.
Export WZY_Poly_Enhance.

Fixpoint poly_get_last (p : poly) : Z := 
  match p with
  | nil => 0
  | a::nil => a
  | h::t => poly_get_last t
  end.

Fact poly_app_nonnil: forall (p : poly) a, (p ++ a::nil) <> nil.
Proof.
  intros. unfold not. intros.
  induction p.
  - inversion H; subst.
  - inversion H; subst.
Qed.

Fact poly_get_last_app: forall (p : poly) a,
  poly_get_last (p ++ a::nil) = a.
Proof.
  intros.
  induction p.
  - simpl. reflexivity.
  - pose proof poly_app_nonnil p a.
    simpl. 
    destruct (p ++ a ::nil).
    + unfold not in H. assert ((nil:poly) = (nil:poly)). { reflexivity. }
      pose proof H H0. destruct H1.
    + tauto.
Qed.

Fact poly_get_last_cons: forall (a h: Z) (t : poly),
  poly_get_last (a::h::t) = poly_get_last (h::t).
Proof.
  intros.
  simpl. reflexivity.
Qed.

Fixpoint poly'_get_first (p : poly) : Z := 
  match p with
  | nil => 0
  | h::t => h
  end.

Definition poly_monomialize (p : poly) : poly :=
  match p with
  | nil => nil
  | _ :: _ => (repeat 0 ((length p) - 1)) ++ (poly_get_last p)::nil
  end.

Definition poly'_monomialize (p : poly') : poly' := 
  match p with
  | nil => nil
  | h :: _ => h::nil ++ (repeat 0 ((length p) - 1))
  end.

Example poly_mono_1: poly_monomialize (3::2::1::nil) = 0::0::1::nil.
Proof.
  simpl. reflexivity.
Qed.

Example poly'_mono_1: poly'_monomialize (1::2::3::nil) = 1::0::0::nil.
Proof.
  simpl. reflexivity.
Qed.

Lemma poly'_eval_mono: forall (p : poly') (n : Z),
  poly'_eval (poly'_monomialize p) n = (poly'_get_first p) * n^(Z.of_nat (length p) - 1).
Proof.
  intros.
  induction p.
  - simpl. reflexivity.
  - assert (Datatypes.length p - 0 = Datatypes.length p)%nat.
    { omega. }
    assert (poly'_eval (poly'_monomialize (a :: p)) n = a * n ^ Z.of_nat (Datatypes.length (repeat 0 (Datatypes.length p - 0))) + poly'_eval (repeat 0 (Datatypes.length p - 0)) n).
    { simpl. reflexivity. }
    rewrite H0. clear H0.
    rewrite H.
    assert (Datatypes.length (repeat 0 (Datatypes.length p)) = Datatypes.length p).
    { clear IHp H.
      induction p.
      - simpl. reflexivity.
      - simpl. rewrite IHp. reflexivity.
    }
    rewrite H0.
    pose proof poly'_eval_0s (Datatypes.length p) n.
    rewrite H1.
    assert (poly'_get_first (a :: p) = a).
    { simpl. reflexivity. }
    rewrite H2.
    assert (Z.of_nat (Datatypes.length (a :: p)) - 1 = Z.of_nat (Datatypes.length p)).
    { assert (Datatypes.length (a :: p) = Datatypes.length p + 1)%nat.
      { simpl. omega. }
      rewrite H3.
      rewrite Nat2Z.inj_add.
      simpl. omega.
    }
    rewrite H3.
    omega.
Qed.

Lemma poly_mono_app_1 : forall (p : poly) a,
  poly_monomialize (p ++ a::nil) = (repeat 0 (length p)) ++ a::nil.
Proof.
  intros.
  pose proof poly_app_nonnil p a.
  pose proof poly_get_last_app p a.
  assert (length (p ++ a::nil) = length p + 1)%nat.
  { clear H H0.
    induction p.
    - simpl. reflexivity.
    - simpl. rewrite IHp. reflexivity.
  }
  unfold poly_monomialize. destruct (p ++ a::nil).
  { unfold not in H. assert ((nil:poly) = (nil:poly)). { reflexivity. }
    pose proof H H2. destruct H3.
  }
  { rewrite H0. rewrite H1.
    assert (Datatypes.length p + 1 - 1 = Datatypes.length p)%nat.
    { omega. }
    rewrite H2.
    reflexivity.
  }
Qed.

Lemma poly'_mono_poly_mono : forall (p : poly') n,
  poly_eval (poly_monomialize (rev p)) n = poly'_eval (poly'_monomialize p) n.
Proof.
  intros.
  induction p.
  - simpl. reflexivity.
  - simpl.
    assert (Datatypes.length p - 0 = Datatypes.length p)%nat.
    { omega. }
    rewrite H.
    assert (Datatypes.length (repeat 0 (Datatypes.length p)) = Datatypes.length p).
    { clear IHp H.
      induction p.
      - simpl. reflexivity.
      - simpl. rewrite IHp. reflexivity.
    }
    rewrite H0.
    pose proof poly'_eval_0s (Datatypes.length p) n.
    rewrite H1.
    pose proof poly_mono_app_1 (rev p) a.
    rewrite H2.
    rewrite rev_length.
    { clear IHp H H0 H1 H2.
      induction p.
      - simpl. omega.
      - simpl. rewrite IHp. 
        assert (n * (a * n ^ Z.of_nat (Datatypes.length p) + 0) = a * n * n ^ Z.of_nat (Datatypes.length p)).
        { simpl. ring. }
        rewrite H.
        pose proof Z.pow_1_r n. rewrite <- H0 at 1. clear H0.
        pose proof Z.pow_add_r n 1 (Z.of_nat (Datatypes.length p)).
        assert (0 <= 1). { omega. }
        assert ( 0 <= Z.of_nat (Datatypes.length p)). { omega. }
        pose proof H0 H1 H2.
        assert (a * n ^ 1 * n ^ Z.of_nat (Datatypes.length p) = a * n ^ (1 + Z.of_nat (Datatypes.length p))).
        { rewrite H3. rewrite Z.mul_assoc. reflexivity. }
        rewrite H4. clear H4.
        pose proof Zpos_P_of_succ_nat (Datatypes.length p).
        rewrite Z.pow_pos_fold.
        rewrite H4.
        assert (1 + Z.of_nat (Datatypes.length p) = Z.succ (Z.of_nat (Datatypes.length p))).
        { rewrite <- Z.add_1_r.
          rewrite Z.add_comm.
          reflexivity.
        }
        rewrite H5.
        omega.
    }
Qed.

Lemma poly_mono_poly'_mono : forall (p : poly) n,
  poly_eval (poly_monomialize p) n = poly'_eval (poly'_monomialize (rev p)) n.
Proof.
  intros.
  pose proof poly'_mono_poly_mono (rev p) n.
  rewrite rev_involutive in H.
  tauto.
Qed.

Lemma poly'_last_poly_first: forall (p : poly'),
  poly_get_last (rev p) = poly'_get_first p.
Proof.
  intros. induction p.
  - simpl. reflexivity.
  - simpl. pose proof poly_get_last_app (rev p) a.
    tauto.
Qed.

Lemma poly_last_poly'_first: forall (p : poly),
  poly_get_last p = poly'_get_first (rev p).
Proof.
  intros. pose proof poly'_last_poly_first (rev p).
  rewrite rev_involutive in H.
  tauto.
Qed.

Lemma poly_eval_mono: forall (p : poly) (n : Z),
  poly_eval (poly_monomialize p) n = (poly_get_last p) * n^(Z.of_nat (length p) - 1).
Proof.
  intros.
  pose proof poly_mono_poly'_mono p n. 
  rewrite H.
  pose proof poly_last_poly'_first p.
  rewrite H0.
  rewrite <- rev_length.
  pose proof poly'_eval_mono (rev p) n.
  tauto.
Qed.

Fixpoint poly_get_max (p : poly) (d : Z) : Z := 
  match p with
    | nil => d
    | b::t => poly_get_max t (Z.max b d)
  end.

Lemma poly_get_max1: forall (p : poly),
  forall z, z <= poly_get_max p z.
Proof.
  induction p; intros.
  - simpl. reflexivity.
  - simpl. 
    specialize (IHp (Z.max a z)).
    assert (z <= Z.max a z).
    { apply Z.le_max_r. }
    pose proof Z.le_trans _ _ _ H IHp.
    tauto.
Qed.

Lemma poly_get_max2: forall (p : poly) z1 z2,
  z1 <= z2 ->
  poly_get_max p z1 <= poly_get_max p z2.
Proof.
  induction p; intros.
  - simpl. tauto.
  - simpl.
    assert ( a <= z1 \/ z1 < a).
    { omega. }
    destruct H0.
    + pose proof Z.max_l _ _ H0.
      rewrite Z.max_comm in H1.
      rewrite H1.
      pose proof Z.le_trans _ _ _ H0 H.
      pose proof Z.max_l _ _ H2.
      rewrite Z.max_comm in H3.
      rewrite H3.
      specialize (IHp z1 z2).
      tauto.
    + apply Z.lt_le_incl in H0.
      pose proof Z.max_l _ _ H0.
      rewrite H1.
      assert ( a <= z2 \/ z2 < a).
      { omega. }
      destruct H2.
      * pose proof Z.max_l _ _ H2.
        rewrite Z.max_comm in H3.
        rewrite H3.
        pose proof IHp a z2 H2.
        tauto.
      * apply Z.lt_le_incl in H2.
        pose proof Z.max_l _ _ H2.
        rewrite H3.
        pose proof IHp a a.
        pose proof Z.le_refl a.
        tauto.
Qed.

Lemma poly_get_max3: forall (p : poly),
  forall z, In z p -> z <= poly_get_max p 0.
Proof.
  induction p; intros.
  - simpl. inversion H.
  - simpl.
    assert (z <= 0 \/ z > 0).
    { omega. }
    destruct H0.
    + pose proof poly_get_max1 p 0.
      pose proof poly_get_max2 p 0 (Z.max a 0).
      pose proof Z.le_max_r a 0.
      pose proof H2 H3.
      pose proof Z.le_trans _ _ _ H0 H1.
      pose proof Z.le_trans _ _ _ H5 H4.
      tauto.
    + inversion H; subst.
      * pose proof poly_get_max1 p z.
        pose proof poly_get_max2 p z (Z.max z 0).
        pose proof Z.le_max_l z 0.
        pose proof H2 H3.
        pose proof Z.le_trans _ _ _ H1 H4.
        tauto.
      * specialize (IHp z).
        pose proof IHp H1.
        pose proof poly_get_max2 p 0 (Z.max a 0).
        pose proof Z.le_max_r a 0.
        pose proof H3 H4.
        pose proof Z.le_trans _ _ _ H2 H5.
        tauto.
Qed.

Fact poly_get_last_in_poly:
  forall (a : Z) p, In (poly_get_last (a::p)) (a::p).
Proof.
  intros a p.
  revert a.
  induction p.
  - simpl. left. omega.
  - intros.
    pose proof poly_get_last_cons a0 a p.
    rewrite H.
    pose proof IHp a.

Admitted.

Lemma poly_distr_coef_compare:
  forall K (N : nat) n,
  K > 0 ->
  n > 0 ->
  poly_eval ((repeat 0 (Z.to_nat (Z.of_nat N-1))) ++ (K * Z.of_nat N)::nil) n >= 
  poly_eval (repeat K N) n.
Proof.
  assert (forall N:nat, (Datatypes.length (repeat 0 N)) = N) as lem_repeat.
  { intros. simpl.
    induction N.
    - simpl. reflexivity.
    - simpl. rewrite IHN. reflexivity.
  }
  intros.
  induction N.
  - simpl. omega.
  - pose proof poly_eval_app (repeat 0 (Z.to_nat (Z.of_nat (S N) - 1))) (K * Z.of_nat (S N) :: nil) n.
    rewrite H1.
    pose proof poly_eval_zero (Z.to_nat (Z.of_nat (S N) - 1)).
    rewrite H2.
    pose proof lem_repeat (Z.to_nat (Z.of_nat (S N) - 1))%nat.
    rewrite H3.
    pose proof Z2Nat.id (Z.of_nat (S N) - 1).
    assert (0 <= Z.of_nat (S N) - 1).
    { clear IHN H1 H2 H3 H4.
      induction N. - simpl. omega.
      - pose proof Nat2Z.inj_succ (S N).
        rewrite H1.
        pose proof Z.le_succ_diag_r (Z.of_nat (S N)).
        omega.
    }
    pose proof H4 H5.
    rewrite H6.
    assert (poly_eval (K * Z.of_nat (S N) :: nil) n = K * Z.of_nat (S N)).
    { simpl. omega. }
    rewrite H7.
    rewrite Z.add_0_l.
    assert (S N = N + 1)%nat. { omega. }
    rewrite H8.
    assert (Z.of_nat (N + 1) - 1 = Z.of_nat N).
    { pose proof Nat2Z.inj_sub (N+1) 1.
      assert (1 <= N + 1)%nat. omega.
      pose proof H9 H10. simpl in H11.
      assert (N+1-1=N)%nat. omega.
      rewrite H12 in H11.
      omega.
    }
    rewrite H9.
    
    clear H1 H2 H3 H4 H5 H6 H7 H8 H9.
    pose proof poly_eval_app (repeat 0 (Z.to_nat (Z.of_nat N - 1))) (K * Z.of_nat N :: nil) n.
    rewrite H1 in IHN.
    pose proof poly_eval_zero (Z.to_nat (Z.of_nat N - 1)) n.
    rewrite H2 in IHN.
    pose proof lem_repeat (Z.to_nat (Z.of_nat N - 1))%nat.
    rewrite H3 in IHN.
    assert (poly_eval (K * Z.of_nat N :: nil) n = K * Z.of_nat N).
    { simpl. omega. }
    rewrite H4 in IHN.
    rewrite Z.add_0_l in IHN.
    assert (Z.to_nat (Z.of_nat N - 1) = N - 1)%nat.
    { pose proof Nat2Z.id N.
      pose proof Z2Nat.inj_sub (Z.of_nat N) 1.
      assert (0<=1). omega. pose proof H6 H7.
      rewrite H5 in H8.
      assert (Z.to_nat 1 = 1)%nat. 
      { simpl. apply Pos2Nat.inj_1. }
      rewrite H9 in H8.
      exact H8.
    }
    rewrite H5 in IHN.
    
    clear H1 H2 H3 H4 H5.
    assert (poly_eval (repeat K (N + 1)) n = K * n ^ (Z.of_nat N) + poly_eval (repeat K N) n).
    { clear IHN.
      induction N.
      - simpl. omega.
      - assert (poly_eval (repeat K (S N + 1)) n = K + n * poly_eval (repeat K (S N)) n).
        { clear IHN. simpl. induction N.
          - simpl. omega.
          - simpl. rewrite IHN. omega.
        }
        rewrite H1.
        assert (S N = N + 1)%nat. omega.
        rewrite <- H2 in IHN.
        rewrite IHN at 1.
        rewrite Z.mul_add_distr_l.
        assert (n * (K * n ^ Z.of_nat N) = K * n ^ (Z.of_nat (S N))).
        { rewrite Z.mul_assoc.
          rewrite Z.mul_shuffle0.
          pose proof Z.pow_1_r n.
          rewrite <- H3 at 1.
          pose proof Z.pow_add_r n 1 (Z.of_nat N).
          assert (0 <= 1). { omega. }
          assert (0 <= Z.of_nat N). { omega. }
          pose proof H4 H5 H6. rewrite <- H7.
          assert (Z.of_nat (S N) = 1 + Z.of_nat N). 
          { pose proof Nat2Z.inj_add 1 N. 
            assert (1 + N = S N)%nat. { omega. }
            assert (1 = Z.of_nat 1). { simpl. omega. }
            rewrite H9 in H8.
            rewrite <- H10 in H8.
            tauto.
          }
          rewrite <- H8. 
          rewrite Z.mul_comm.
          omega.
        }
        rewrite H3.
        rewrite Z.add_assoc.
        assert (K + K * n ^ Z.of_nat (S N) + n * poly_eval (repeat K N) n = K * n ^ Z.of_nat (S N) + (K + n * poly_eval (repeat K N) n)).
        { omega. }
        rewrite H4.
        assert (K + n * poly_eval (repeat K N) n = poly_eval (repeat K (S N)) n).
        { simpl. omega. }
        rewrite H5.
        omega.
      }
      rewrite H1.
      assert (n ^ Z.of_nat N * (K * Z.of_nat (N + 1)) >= n ^ Z.of_nat (N - 1) * (K * Z.of_nat N) + K * n ^ Z.of_nat N).
      { clear H1.
        assert (Z.of_nat (N + 1) = Z.of_nat N + 1). 
        { pose proof Nat2Z.inj_add N 1. simpl in H1. 
          tauto.
        }
        rewrite H1.
        rewrite Z.mul_add_distr_l.
        rewrite Z.mul_add_distr_l.
        assert (n >= 1). { omega. }
        assert (n ^ Z.of_nat N >= n ^ Z.of_nat (N - 1)).
        { clear IHN H1.
          induction N.
          - simpl. omega.
          - assert (n ^ Z.of_nat (S N) = n * n ^ Z.of_nat N).
            { assert (S N = N + 1)%nat. omega.
              rewrite H1. clear H1.
              assert (Z.of_nat (N + 1) = Z.of_nat N + 1). 
              { pose proof Nat2Z.inj_add N 1. simpl in H1. 
                tauto.
              }
              rewrite H1. clear H1.
              pose proof Z.pow_add_r n (Z.of_nat N) 1.
              assert (0 <= Z.of_nat N). omega.
              assert (0 <= 1). omega.
              pose proof H1 H3 H4. rewrite H5.
              rewrite Z.pow_1_r.
              rewrite Z.mul_comm.
              reflexivity.
            }
            rewrite H1.
            assert (S N - 1 = N)%nat. omega.
            rewrite H3.
            pose proof Z.le_mul_diag_r (n ^ Z.of_nat N) n.
            assert (0 < n ^ Z.of_nat N).
            { apply Z.pow_pos_nonneg. omega. omega. }
            assert (1<=n). omega.
            pose proof H4 H5.
            apply H7 in H6.
            rewrite Z.mul_comm in H6.
            omega.
        }
        assert (n ^ Z.of_nat N * (K * 1) = K * n ^ Z.of_nat N).
        { ring. }
        rewrite H4.
        apply Z.le_ge.
        pose proof Zplus_le_compat_r (n ^ Z.of_nat (N - 1) * (K * Z.of_nat N)) (n ^ Z.of_nat N * (K * Z.of_nat N)) (K * n ^ Z.of_nat N).
        assert (n ^ Z.of_nat (N - 1) * (K * Z.of_nat N) <= n ^ Z.of_nat N * (K * Z.of_nat N)).
        { clear H5. 
          pose proof Z.mul_le_mono_nonneg_r (n ^ Z.of_nat (N - 1)) (n ^ Z.of_nat N) (K * Z.of_nat N).
          assert (0 <= K * Z.of_nat N ).
          pose proof Z.mul_nonneg_nonneg K (Z.of_nat N).
          assert (0<=K). omega. pose proof H6 H7.
          assert (0<=Z.of_nat N). omega. pose proof H8 H9.
          exact H10.
          pose proof H5 H6.
          assert (n ^ Z.of_nat (N - 1) <= n ^ Z.of_nat N). omega.
          tauto.
        }
     pose proof H5 H6.
     tauto.
   }
   assert (n ^ Z.of_nat (N - 1) * (K * Z.of_nat N) + K * n ^ Z.of_nat N >= K * n ^ Z.of_nat N + poly_eval (repeat K N) n).
   { apply Z.le_ge.
     pose proof Zplus_le_compat_l (poly_eval (repeat K N) n) (n ^ Z.of_nat (N - 1) * (K * Z.of_nat N)) (K * n ^ Z.of_nat N).
     apply Z.ge_le in IHN.
     pose proof H3 IHN. omega.
   }
  omega.
Qed.

Fact poly_mono_cons: forall a h t,
  poly_monomialize (a :: h :: t) = 0 :: poly_monomialize (h :: t).
Proof.
  intros.
  simpl.
  assert (Datatypes.length t - 0 = Datatypes.length t)%nat.
  omega.
  rewrite H.
  reflexivity.
Qed.

Fact poly_mono_length_invar: forall p : poly,
  length p = length (poly_monomialize p).
Proof.
  intros.
  induction p.
  - simpl. omega.
  - destruct p.
    + simpl. reflexivity.
    + pose proof poly_mono_cons a z p.
      rewrite H.
      assert (Datatypes.length (a :: z :: p) = 1 + Datatypes.length (z :: p))%nat. { simpl. omega. }
      assert (Datatypes.length (0 :: poly_monomialize (z :: p)) = plus 1 (Datatypes.length (poly_monomialize (z :: p)))).
      { simpl. reflexivity. }
      rewrite H0.
      rewrite H1.
      f_equal.
      omega.
Qed.

Definition term_by_term_le := list_le.

Lemma poly_each_coef_compare:
  forall p1 p2,
  length p1 = length p2 ->
  term_by_term_le p1 p2 ->
  forall n, 0 <= n ->
  poly_eval p1 n <= poly_eval p2 n.
Proof.
  intros.
  induction H0.
  - omega.
  - simpl.
    pose proof IHlist_le H0.
    apply Z.add_le_mono; auto.
    apply Z.mul_le_mono_nonneg_l; auto.
Qed.

End Monomial.

Module Polynomial_Asympotitic_Bound.
Export Polynomial.
Export Monomial.
Import Assertion_D.

Inductive AsymptoticBound : Type :=
  | BigO : poly -> logical_var -> AsymptoticBound
  | BigOmega : poly -> logical_var -> AsymptoticBound
  | BigTheta : poly -> logical_var -> AsymptoticBound.

Definition ab_eval (La : Lassn) (T : AsymptoticBound) (a1 a2 t : Z) : Prop :=
  match T with
  | BigO p n => 0 < La n ->
                0 <= t <= a2 * (poly_eval p (La n))
  | BigOmega p n => 0 < La n ->
                    0 <= a1 * (poly_eval p (La n)) <= t
  | BigTheta p n => 0 < La n ->
                    0 <= a1 * (poly_eval p (La n)) <= t /\ t <= a2 * (poly_eval p (La n))
  end.

Reserved Notation "T1 '=<' T2" (at level 50, no associativity).

Inductive loosen : AsymptoticBound -> AsymptoticBound -> Prop :=
  | Theta2Omega : forall p n, 0 < poly_get_last p -> BigTheta p n =< BigOmega p n
  | Theta2O : forall p n, 0 < poly_get_last p -> BigTheta p n =< BigO p n
  (* | HighestEquivO : forall p1 p2 n,
                      0 < poly_coef_sum p1 ->
                      0 < poly_coef_sum p2 ->
                      length p1 = length p2 ->
                      BigO p1 n =< BigO p2 n*)
  | O_Poly2Mono : forall p n, 0 < poly_get_last p -> BigO p n =< BigO (poly_monomialize p) n
  (* TODO: more highest equiv loosenings *)
  (* TODO: other loosenings *)
  
  where "T1 '=<' T2" := (loosen T1 T2).
  

End Polynomial_Asympotitic_Bound.
