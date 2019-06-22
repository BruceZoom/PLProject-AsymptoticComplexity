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

Fixpoint poly_pick_highest_coef (p : poly) : Z :=
  match p with
  | nil => 0
  | h::t => (poly_pick_highest_coef t)
  end. 
  
(* Comparation of values of poly_eval *)
Inductive poly_all_coef_lt (p1 p2: poly)

Fact poly_lt_if_all_coef_lt: forall (p1 p2: poly)

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
  | BigO p n => N <= La n ->
                0 <= t <= a2 * (poly_eval p (La n))
  | BigOmega p n => N <= La n ->
                    0 <= a1 * (poly_eval p (La n)) <= t
  | BigTheta p n => N <= La n ->
                    0 <= a1 * (poly_eval p (La n)) <= t /\ t <= a2 * (poly_eval p (La n))
  end.

Reserved Notation "T1 '=<' T2" (at level 50, no associativity).

Inductive loosen : AsymptoticBound -> AsymptoticBound -> Prop :=
  | Theta2Omega : forall p n, BigTheta p n =< BigOmega p n
  | Theta2O : forall p n, BigTheta p n =< BigO p n
  | HighestEquivO : forall p1 p2 n,
                      length p1 = length p2 ->
                      BigO p1 n =< BigO p2 n
  (* TODO: more highest equiv loosenings *)
  (* TODO: other loosenings *)
  
  where "T1 '=<' T2" := (loosen T1 T2).

End Polynomial_Asympotitic_Bound.
