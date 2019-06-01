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

Lemma poly_add_eval_comm : forall p1 p2 z,
  poly_eval (poly_add p1 p2) z = poly_eval p1 z + poly_eval p2 z.
Proof.
  intro p1.
  induction p1; intros.
  - simpl. rewrite poly_add_empty_l. reflexivity.
  - (* TODO: FILL IN HERE *) Admitted.
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
  (exists (a1 a2 N : Z), a1 < 0 -> a2 < 0 -> N < 0 ->
    forall La t, ab_eval La T1 a1 a2 N t) ->
  exists (a1' a2' N' : Z), a1' < 0 -> a2' < 0 -> N' < 0 ->
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
