Require Import AB.Imp8.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Open Scope Z.

Module Polynomial.
Import Assertion_D.

Definition poly := list Z. (* The power decreases as the index goes up *)

(** Evaluations of polynomial *)
Fixpoint poly_eval (p : poly) : Z -> Z :=
  fun z =>
    match p with
    | nil => 0
    | h :: t => h * (Z.pow z (Z.of_nat (length t))) + (poly_eval t z)
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
    | h :: t => h * (TPower v (length t)) + (poly_eval_lv t v)
    end.

Close Scope term_scope.
(** [] *)

(** Operations of polynomial *)
Fixpoint poly_add_body (l1 l2 : list Z) : list Z :=
  match l1, l2 with
  | nil, nil => l2
  | h::t, nil => h::t
  | nil, h::t => h::t
  | h::t, h'::t' => (h+h')::(poly_add_body t t')
  end.

Definition poly_add (p1 p2 : poly) : poly := rev (poly_add_body (rev p1) (rev p2)).

Fixpoint poly_mult (p1 p2 : poly) : poly :=
  match p1 with
  | nil => nil
  | h :: t => poly_add (app p2 (repeat 0 (length t))) (poly_mult t p2)
  end.

Fixpoint trim_0_l (p : poly) : poly :=
  match p with
  | nil => nil
  | h :: t => if Z.eq_dec h 0 then trim_0_l t else h :: t
  end.

Theorem trim_invar:
  forall p n,
  poly_eval (trim_0_l p) n = poly_eval p n.
Proof.
  intros p.
  induction p.
  - intros. simpl. reflexivity.
  - intros.
    simpl. destruct (Z.eq_dec a 0) eqn:eq.
    + pose proof IHp n.
      rewrite H. rewrite e.
      simpl. reflexivity.
    + simpl. reflexivity.
Qed.

Definition highest_nonneg (p : poly) : Prop :=
  match trim_0_l p with
  | nil => True
  | h :: t => h >= 0
  end.
(** [] *)

Example poly_add_eg : poly_eval (poly_add (1::1::nil) (1::0::1::nil)) 2 = 8.
Proof.
  simpl. reflexivity.
Qed.

Example poly_mult_eg : poly_eval (poly_mult (1::1::nil) (1::0::1::nil)) 2 = 15.
Proof.
  simpl. reflexivity.
Qed.

(** Properties of Polynomial Operations *)
Lemma poly_add_body_empty_r : forall l, poly_add_body l nil = l.
Proof.
  intros.
  destruct l.
  - auto.
  - simpl. reflexivity.
Qed.

Lemma poly_add_empty_r : forall p, poly_add p nil = p.
Proof.
  intros.
  destruct p.
  - auto.
  - unfold poly_add.
    rewrite poly_add_body_empty_r.
    apply rev_involutive.
Qed.

Lemma poly_add_body_empty_l : forall l, poly_add_body nil l = l.
Proof.
  intros.
  destruct l.
  - auto.
  - simpl. reflexivity.
Qed.

Lemma poly_add_empty_l : forall p, poly_add nil p = p.
Proof.
  intros.
  destruct p.
  - auto.
  - unfold poly_add.
    rewrite poly_add_body_empty_l.
    apply rev_involutive.
Qed.

Lemma poly_eval_0s: forall times n,
  poly_eval (repeat 0 times) n = 0.
Proof.
  intros.
  induction times.
  - simpl. reflexivity.
  - simpl. omega.
Qed.

Lemma poly_cons_eval_comm : forall p z n,
  poly_eval (cons z p) n = poly_eval (cons z (repeat 0 (length p))) n + poly_eval p n.
Proof.
  intros.
  simpl.
  assert (Datatypes.length (repeat 0 (Datatypes.length p)) = Datatypes.length p).
  { induction p.
    - simpl. reflexivity.
    - simpl. rewrite IHp. reflexivity.
  }
  rewrite H.
  pose proof poly_eval_0s (Datatypes.length p) n.
  rewrite H0.
  omega.
Qed.

Lemma poly_app_eval_comm: forall p1 p2 n,
  poly_eval (p1 ++ p2) n = poly_eval (p1 ++ (repeat 0 (length p2))) n + poly_eval p2 n.
Proof.
  intros.
  induction p1.
  - simpl. Search (nil ++ _).
    pose proof app_nil_l p2.
    rewrite <- H. simpl.
    pose proof poly_eval_0s (Datatypes.length p2) n.
    rewrite H0.
    omega.
  - pose proof poly_cons_eval_comm.
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

Lemma poly_eval_repeat_length_p: forall a (p : poly) z,
  poly_eval (a :: repeat 0 (length p)) z = a * z ^ (Z.of_nat (length p)).
Proof.
  intros.
  simpl.
  pose proof poly_eval_0s (length p) z.
  rewrite H.
  pose proof repeat_length 0 (length p).
  rewrite H0.
  omega.
Qed.

Lemma poly_add_body_comm: forall p1 p2,
  poly_add_body p1 p2 = poly_add_body p2 p1.
Proof.
  intro.
  induction p1; intros.
  - rewrite poly_add_body_empty_l.
    rewrite poly_add_body_empty_r.
    reflexivity.
  - induction p2.
    + rewrite poly_add_body_empty_l.
      rewrite poly_add_body_empty_r.
      reflexivity.
    + simpl.
      rewrite IHp1.
      rewrite Z.add_comm.
      reflexivity.
Qed.

Lemma poly_add_comm : forall p1 p2,
  poly_add p1 p2 = poly_add p2 p1.
Proof.
  intros.
  unfold poly_add.
  rewrite poly_add_body_comm.
  reflexivity.
Qed.

Lemma poly_add_body_cons_split : forall a p,
  p ++ a :: nil = poly_add_body p ((repeat 0 (length p)) ++ a :: nil).
Proof.
  intros. revert a.
  induction p; intros.
  - simpl. reflexivity.
  - simpl. rewrite <- IHp. rewrite Z.add_0_r. reflexivity.
Qed.

Lemma repeat_head_tail : forall (z : Z) n, z :: repeat z n = repeat z n ++ z :: nil.
Proof.
  intros.
  induction n.
  - auto.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma rev_repeat : forall (z : Z) n, rev (repeat z n) = repeat z n.
Proof.
  intros.
  induction n.
  - auto.
  - simpl. rewrite IHn. rewrite repeat_head_tail. reflexivity.
Qed.

Lemma poly_add_body_same_level_tail : forall p1 p2 a1 a2,
  length p1 = length p2 ->
  poly_add_body (p1 ++ a1 :: nil) (p2 ++ a2 :: nil) = poly_add_body p1 p2 ++ (a1 + a2) :: nil.
Proof.
Admitted.

Lemma poly_add_cons_split : forall a p,
  a::p = poly_add (a :: (repeat 0 (length p))) p.
Proof.
  intros. revert a.
  induction p; intros.
  - simpl. rewrite poly_add_empty_r. reflexivity.
  - unfold poly_add in *. simpl in *. rewrite rev_repeat in *.
Admitted.

Lemma poly_add_assoc : forall p1 p2 p3,
  poly_add (poly_add p1 p2) p3 = poly_add p1 (poly_add p2 p3).
Admitted.

Lemma zero_poly : forall n z, poly_eval (repeat 0 n) z = 0.
Proof.
Admitted.

Lemma extract_single_term : forall a p z n, poly_eval (poly_add (a :: repeat 0 n) p) z = a * z ^ Z.of_nat n + poly_eval p z.
Proof.
  intros.
  revert a. revert n.
  induction p; intros.
  - rewrite poly_add_empty_r. simpl. rewrite zero_poly, repeat_length. reflexivity.
  - Admitted.

Lemma poly_add_eval_comm : forall p1 p2 z,
  poly_eval (poly_add p1 p2) z = poly_eval p1 z + poly_eval p2 z.
(*Proof.
  intro.
  induction p1; intros.
  - simpl. rewrite poly_add_empty_l. reflexivity.
  - rewrite poly_add_cons_split.
    assert (poly_add (a :: repeat 0 (Datatypes.length p1)) p1 = poly_add p1 (a :: repeat 0 (Datatypes.length p1))). rewrite poly_add_comm. auto.
    rewrite H; clear H. rewrite poly_add_assoc, IHp1, IHp1.
    rewrite <- Z.add_assoc. f_equal.
    (*remember (a :: repeat 0 (Datatypes.length p1)) as p0.*)
    induction p2.
    + rewrite poly_add_empty_r. simpl. omega.
    + rewrite poly_add_cons_split. *)
(** Proof.
  intro p1.
  induction p1; intros.
  - simpl. rewrite poly_add_empty_l. reflexivity.
  - simpl. pose proof IHp1 p2 z.
    assert (a * z ^ Z.of_nat (Datatypes.length p1) + poly_eval p1 z + poly_eval p2 z =
    a * z ^ Z.of_nat (Datatypes.length p1) + poly_eval (poly_add p1 p2) z).
    { omega. }
    rewrite H0. clear H0.
    pose proof IHp1 (a::p1) z.
    simpl in H0.
**)
Proof.
  intros. revert p2.
  induction p1; intros.
  - simpl. rewrite poly_add_empty_l. reflexivity.
  - simpl.
    rewrite <- Z.add_assoc.
    rewrite <- IHp1.
    rewrite poly_add_cons_split, poly_add_assoc.
    remember (poly_add p1 p2) as p3.
    clear Heqp3.
    remember (Datatypes.length p1) as n.
    clear Heqn.
    revert a.
    induction n; intros.
    + simpl.
    (*
    pose proof poly_cons_eval_comm p1 a z.
    pose proof poly_eval_repeat_length_p a p1 z.
    rewrite <- H0.
    *)
    
  (* TODO: FILL IN HERE *) Abort.
(** [] *)

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
  | HighestEquivTheta : forall p1 p2 n,
                      length (trim_0_l p1) = length (trim_0_l p2) ->
                      BigTheta p1 n =< BigTheta p2 n
  (* TODO: more highest equiv loosenings *)
  (* TODO: other loosenings *)
  
  where "T1 '=<' T2" := (loosen T1 T2).

(* TODO: prove loosening correctness *)
Theorem loosen_valid :
  forall T1 T2, T1 =< T2 ->
  (exists (a1 a2 N : Z), 0 < a1 -> 0 < a2 -> 0 < N ->
    forall La t, ab_eval La T1 a1 a2 N t) ->
  exists (a1' a2' N' : Z), 0 < a1' -> 0 < a2' -> 0 < N' ->
    forall La t, ab_eval La T2 a1' a2' N' t.
Proof.
  intros. revert H0.
  induction H; intros [a1 [a2 [N ?]]]; simpl in *;
  try (exists a1, a2, N;
      intros;
      pose proof H H0 H1 H2 La t H3; omega).
  (* Prove the polynomial asymptotic bounds are equivalent when the highest orders are the same *)
  - (* HighestEquivTheta *)
    simpl in *.
    
  Admitted.


End Polynomial_Asympotitic_Bound.
