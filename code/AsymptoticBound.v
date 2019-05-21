Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Require Import Omega.


Module NatAttempt.

Definition ABigOmega (f g : nat -> nat) : Prop :=
  exists a, a > 0 ->
  exists N, forall n, N < n ->
    g n <= a * (f n).

Definition ABigO (f g : nat -> nat) : Prop :=
  exists a, a > 0 ->
  exists N, forall n, N < n ->
    f n <= a * (g n).

Definition ABigTheta (f g : nat -> nat) : Prop :=
  ABigOmega f g /\ ABigO f g.

(** An example for asymptotic bound of cubic function *)
Definition cube1 : nat -> nat := fun x => x*x*x.
Definition poly1 : nat -> nat := fun x => 3*(x*x*x) + x*x - x.

Example boungs_eg1 : ABigTheta poly1 cube1.
Proof.
  unfold ABigTheta, ABigOmega, ABigO, cube1, poly1.
  split.
  - exists 1; intros.
    exists 1; intros.
    simpl. repeat rewrite <- plus_n_O.
    repeat rewrite Nat.mul_add_distr_r.
    rewrite <- Nat.add_sub_assoc.
    + rewrite <- Nat.add_assoc.
      apply le_plus_l.
    + rewrite <- Nat.mul_1_r at 1.
      apply Nat.mul_le_mono_l.
      omega.
  - exists 4; intros.
    exists 0; intros.
    assert (4 = 3 + 1). omega.
    rewrite H1, Nat.mul_add_distr_r; clear H1.
    assert (n <= n*n).
    {
      rewrite <- Nat.mul_1_r at 1.
      apply Nat.mul_le_mono_l.
      omega.
    }
    rewrite <- Nat.add_sub_assoc; [| apply H1].
    Search (_+_<=_+_).
    apply plus_le_compat_l.
    simpl. rewrite <- plus_n_O.
    assert (n = n * 1). omega.
    rewrite H2 at 3; clear H2.
    rewrite <- Nat.mul_sub_distr_l.
    rewrite <- Nat.mul_assoc.
    apply mult_le_compat_l.
    eapply le_trans; [| apply H1]. omega.
Qed.

End NatAttempt.


Module ZAttempt.

Open Scope Z.

Definition ABigOmega (f g : Z -> Z) : Prop :=
  exists (a : Z), a > 0 ->
  exists (N : Z), forall (n : Z), N < n ->
    g n <= a * (f n).

Definition ABigO (f g : Z -> Z) : Prop :=
  exists a, a > 0 ->
  exists N, forall n, N < n ->
    f n <= a * (g n).

Definition ABigTheta (f g : Z -> Z) : Prop :=
  ABigOmega f g /\ ABigO f g.

(** An example for asymptotic bound of cubic function *)
Definition cube1 : Z -> Z := fun x => x*x*x.
Definition poly1 : Z -> Z := fun x => 3*(x*x*x) + x*x - x.

Example boungs_eg1 : ABigTheta poly1 cube1.
Proof.
  unfold ABigTheta, ABigOmega, ABigO, cube1, poly1.
  split.
  - exists 1; intros.
    exists 1; intros.
    rewrite Z.mul_1_l.
    rewrite <- (Z.mul_1_r n) at 9.
    rewrite <- Z.add_sub_assoc.
    rewrite <- Z.mul_sub_distr_l.
    assert (0 <= n * (n - 1)).
    {
      apply (Z.mul_nonneg_nonneg n (n-1)).
      omega. omega.
    }
    assert (n*n*n <= 3*(n*n*n)).
    {
      rewrite <- (Z.mul_1_l (n*n*n)) at 1.
      apply (Z.mul_le_mono_nonneg_r 1 3 (n*n*n)); [| omega].
      apply Z.mul_nonneg_nonneg.
      apply Z.square_nonneg.
      omega.
    }
    omega.
  - exists 4; intros.
    exists 0; intros.
    (* split 3 * (n * n * n) + 1 * (n * n * n) *)
    assert (4 = 3 + 1). omega.
    rewrite H1; clear H1.
    rewrite Z.mul_add_distr_r.
    (* remove 3 * (n * n * n) *)
    rewrite <- Z.add_sub_assoc.
    apply Zplus_le_compat_l.
    (* remove n *)
    rewrite Z.mul_1_l.
    rewrite <- (Z.mul_1_r n) at 3.
    rewrite <- Z.mul_sub_distr_l.
    rewrite <- Z.mul_assoc.
    apply Z.mul_le_mono_nonneg_l; [omega |].
    (* n - 1 <= n <= n * n *)
    apply Z.le_trans with n; [omega |].
    rewrite <- (Z.mul_1_r n) at 1.
    apply Z.mul_le_mono_nonneg_l; omega.
Qed.

End ZAttempt.
