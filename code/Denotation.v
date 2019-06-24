Require Import Coq.Lists.List.
Require Import AB.Imp9.

Module Command_Denotation_With_Steps.
Import Assertion_D.

(* Here we assume that every elementary command will cost time, more specifically, SKIP command should take 1 time steps instead of 0. *)

Definition skip_sem: state -> Z -> state -> Prop :=
  fun st1 t st2 =>
    st1 = st2 /\ t = 1.                             (* <-- modified *)

(* Originally the t is dependent with Y, here we move t out and is an independent conjunction branch. *)

Definition asgn_sem (X: var) (E: aexp): state -> Z -> state -> Prop :=
  fun st1 t st2 =>
    st2 X = aeval E st1 /\
    (forall Y, X <> Y -> st1 Y = st2 Y) /\          (* <-- modified *)
    t = 1.

Definition seq_sem (d1 d2: state -> Z -> state -> Prop)
  : state -> Z -> state -> Prop
:=
  fun st1 t st3 =>
    exists t1 t2 st2,
      d1 st1 t1 st2 /\ d2 st2 t2 st3 /\ t = t1 + t2.

Definition if_sem (b: bexp) (d1 d2: state -> Z -> state -> Prop)
  : state -> Z -> state -> Prop
:=
  fun st1 t st2 =>
    (d1 st1 t st2 /\ beval b st1) \/
    (d2 st1 t st2 /\ ~beval b st1).                 (* <-- modified *)

Fixpoint iter_loop_body
  (b: bexp)
  (loop_body: state -> Z -> state -> Prop)
  (n: nat)
  : state -> Z -> state -> Prop
:=
  match n with
  | O =>
     fun st1 t st2 =>
       (st1 = st2 /\ t = 0) /\ ~beval b st1         (* <-- modified *)
  | S n' =>
     fun st1 t st3 =>
       (exists t1 t2 st2,
         (loop_body) st1 t1 st2 /\
         (iter_loop_body b loop_body n') st2 t2 st3 /\
         t = t1 + t2) /\
       beval b st1
  end.

Definition loop_sem (b: bexp) (loop_body: state -> Z -> state -> Prop)
  : state -> Z -> state -> Prop
:=
  fun st1 t st2 =>
    exists n, (iter_loop_body b loop_body n) st1 t st2.

Fixpoint ceval (c: com): state -> Z -> state -> Prop :=
  match c with
  | CSkip => skip_sem
  | CAss X E => asgn_sem X E
  | CSeq c1 c2 => seq_sem (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c => loop_sem b (ceval c)
  end.

Theorem command_cost_time : forall c st1 st2 t,
  ceval c st1 t st2 -> 0 < t.
Proof.
Abort.
(*   intro.
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
Qed. *)

End Command_Denotation_With_Steps.
