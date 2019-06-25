(** (This following part of this file is copied from <<Software Foundation>>
volume 1. It should be only used for lecture notes and homework assignments for
course CS263 of Shanghai Jiao Tong University, 2019 spring. Any other usage are
not allowed. For the material of thses parts, please refer to the original
book.) *)

Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.ZArith.ZArith.
Require Export Coq.Strings.String.
Require Export Coq.Logic.Classical.

Arguments clos_refl_trans {A} _ _ _.
Arguments clos_refl_trans_1n {A} _ _ _.
Arguments clos_refl_trans_n1 {A} _ _ _.

Open Scope Z.

Definition var: Type := nat.

Inductive aexp : Type :=
  | ANum (n : Z)
  | AId (X : var)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion ANum : Z >-> aexp.

Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.

Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x == y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'!' b" := (BNot b) (at level 39, right associativity) : imp_scope.

Inductive com : Type :=
  | CSkip
  | CAss (X: var) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Bind Scope imp_scope with com.
Notation "'Skip'" :=
   CSkip : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'While' b 'Do' c 'EndWhile'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'If' c1 'Then' c2 'Else' c3 'EndIf'" :=
  (CIf c1 c2 c3) (at level 10, right associativity) : imp_scope.

Module Abstract_Pretty_Printing.
Coercion AId: var >-> aexp.
Notation "x '::=' a" :=
  (CAss x a) (at level 80) : imp_scope.
End Abstract_Pretty_Printing.

Module Relation_Operators.

Definition id {A: Type}: A -> A -> Prop := fun a b => a = b.

Definition empty {A B: Type}: A -> B -> Prop := fun a b => False.

Definition concat {A B C: Type} (r1: A -> B -> Prop) (r2: B -> C -> Prop): A -> C -> Prop :=
  fun a c => exists b, r1 a b /\ r2 b c.

Definition filter1 {A B: Type} (f: A -> Prop): A -> B -> Prop :=
  fun a b => f a.

Definition filter2 {A B: Type} (f: B -> Prop): A -> B -> Prop :=
  fun a b => f b.

Definition union {A B: Type} (r1 r2: A -> B -> Prop): A -> B -> Prop :=
  fun a b => r1 a b \/ r2 a b.

Definition intersection {A B: Type} (r1 r2: A -> B -> Prop): A -> B -> Prop :=
  fun a b => r1 a b /\ r2 a b.

Definition omega_union {A B: Type} (rs: nat -> A -> B -> Prop): A -> B -> Prop :=
  fun st1 st2 => exists n, rs n st1 st2.

End Relation_Operators.

Import Relation_Operators.

Definition state: Type := nat -> Z.

Fixpoint aeval (a : aexp) (st : state) : Z :=
  match a with
  | ANum n => n
  | AId X => st X
  | APlus a1 a2 => (aeval a1 st) + (aeval a2 st)
  | AMinus a1 a2  => (aeval a1 st) - (aeval a2 st)
  | AMult a1 a2 => (aeval a1 st) * (aeval a2 st)
  end.

Definition aexp_dequiv (d1 d2: state -> Z): Prop :=
  forall st, d1 st = d2 st.

Definition aexp_equiv (a1 a2: aexp): Prop :=
  aexp_dequiv (aeval a1) (aeval a2).

Fixpoint beval (b : bexp) (st : state) : Prop :=
  match b with
  | BTrue       => True
  | BFalse      => False
  | BEq a1 a2   => (aeval a1 st) = (aeval a2 st)
  | BLe a1 a2   => (aeval a1 st) <= (aeval a2 st)
  | BNot b1     => ~ (beval b1 st)
  | BAnd b1 b2  => (beval b1 st) /\ (beval b2 st)
  end.

Definition if_sem
  (b: bexp)
  (then_branch else_branch: state -> state -> Prop)
  : state -> state -> Prop
:=
  union
    (intersection then_branch (filter1 (beval b)))
    (intersection else_branch (filter1 (beval (BNot b)))).

Fixpoint iter_loop_body
  (b: bexp)
  (loop_body: state -> state -> Prop)
  (n: nat)
  : state -> state -> Prop
:=
  match n with
  | O =>
         intersection
           id
           (filter1 (beval (BNot b)))
  | S n' =>
            intersection
              (concat
                loop_body
                (iter_loop_body b loop_body n'))
              (filter1 (beval b))
  end.

Definition loop_sem (b: bexp) (loop_body: state -> state -> Prop)
  : state -> state -> Prop
:=
  omega_union (iter_loop_body b loop_body).

Fixpoint ceval (c: com): state -> state -> Prop :=
  match c with
  | CSkip => id
  | CAss X E =>
      fun st1 st2 =>
        st2 X = aeval E st1 /\
        forall Y, X <> Y -> st1 Y = st2 Y
  | CSeq c1 c2 => concat (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c => loop_sem b (ceval c)
  end.

Definition com_dequiv (d1 d2: state -> state -> Prop): Prop :=
  forall st1 st2, d1 st1 st2 <-> d2 st1 st2.

Definition cequiv (c1 c2: com): Prop :=
  com_dequiv (ceval c1) (ceval c2).

Theorem loop_recur: forall b loop_body,
  com_dequiv
    (loop_sem b loop_body)
    (union
      (intersection
        (concat loop_body
          (loop_sem b loop_body))
        (filter1 (beval b)))
      (intersection
        id
        (filter1 (beval (BNot b))))).
Proof.
  intros.
  unfold com_dequiv.
  intros.
  split.
  + intros.
    unfold loop_sem, omega_union in H.
    unfold union.
    destruct H as [n H].
    destruct n as [| n'].
    - right.
      simpl in H.
      exact H.
    - left.
      simpl in H.
      unfold concat, intersection in H.
      unfold concat, intersection.
      destruct H as [[st' [? ?]] ?].
      split.
      * exists st'.
        split.
        { exact H. }
        unfold loop_sem, omega_union.
        exists n'.
        exact H0.
      * exact H1.
  + intros.
    unfold loop_sem, omega_union.
    unfold union in H.
    destruct H.
    - unfold intersection, concat in H.
      destruct H as [[st' [? ?]] ?].
      unfold loop_sem, omega_union in H0.
      destruct H0 as [n ?].
      exists (S n).
      simpl.
      unfold intersection, concat.
      split.
      * exists st'.
        split.
        { exact H. }
        { exact H0. }
      * exact H1.
    - exists O.
      simpl.
      exact H.
Qed.

Lemma refl_com_dequiv : forall (d : state -> state -> Prop),
  com_dequiv d d.
Proof.
  unfold com_dequiv.
  intros.
  tauto.
Qed.

Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof.
  unfold cequiv.
  intros.
  apply refl_com_dequiv.
Qed.

Lemma sym_com_dequiv : forall (d1 d2: state -> state -> Prop),
  com_dequiv d1 d2 -> com_dequiv d2 d1.
Proof.
  unfold com_dequiv.
  intros.
  specialize (H st1 st2).
  tauto.
Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv.
  intros.
  apply sym_com_dequiv.
  exact H.
Qed.

Lemma trans_com_dequiv : forall (d1 d2 d3 : state -> state -> Prop),
  com_dequiv d1 d2 -> com_dequiv d2 d3 -> com_dequiv d1 d3.
Proof.
  unfold com_dequiv.
  intros.
  specialize (H st1 st2).
  specialize (H0 st1 st2).
  tauto.
Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv.
  intros.
  pose proof trans_com_dequiv _ _ _ H H0.
  exact H1.
Qed.

Lemma concat_congruence: forall (d1 d2 d1' d2': state -> state -> Prop),
  com_dequiv d1 d1' ->
  com_dequiv d2 d2' ->
  com_dequiv (concat d1 d2) (concat d1' d2').
Proof.
  unfold com_dequiv.
  intros.
  unfold concat.
  split; intros H1; destruct H1 as [st [? ?]].
  + exists st.
    split.
    - specialize (H st1 st).
      tauto.
    - specialize (H0 st st2).
      tauto.
  + exists st.
    split.
    - specialize (H st1 st).
      tauto.
    - specialize (H0 st st2).
      tauto.
Qed.

Lemma intersection_congruence: forall (d1 d2 d1' d2': state -> state -> Prop),
  com_dequiv d1 d1' ->
  com_dequiv d2 d2' ->
  com_dequiv (intersection d1 d2) (intersection d1' d2').
Proof.
  unfold com_dequiv.
  intros.
  unfold intersection.
  specialize (H st1 st2).
  specialize (H0 st1 st2).
  tauto.
Qed.

Lemma union_congruence: forall (d1 d2 d1' d2': state -> state -> Prop),
  com_dequiv d1 d1' ->
  com_dequiv d2 d2' ->
  com_dequiv (union d1 d2) (union d1' d2').
Proof.
  unfold com_dequiv.
  intros.
  unfold union.
  specialize (H st1 st2).
  specialize (H0 st1 st2).
  tauto.
Qed.

Lemma omega_union_congruence: forall (ds1 ds2: nat -> state -> state -> Prop),
  (forall n, com_dequiv (ds1 n) (ds2 n)) ->
  com_dequiv (omega_union ds1) (omega_union ds2).
Proof.
  unfold com_dequiv.
  intros.
  unfold omega_union.
  split; intros H0; destruct H0 as [n ?]; exists n.
  + specialize (H n st1 st2).
    tauto.
  + specialize (H n st1 st2).
    tauto.
Qed.

Inductive aexp_halt: aexp -> Prop :=
  | AH_num : forall n, aexp_halt (ANum n).

Inductive astep : state -> aexp -> aexp -> Prop :=
  | AS_Id : forall st X,
      astep st
        (AId X) (ANum (st X))

  | AS_Plus1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      astep st
        (APlus a1 a2) (APlus a1' a2)
  | AS_Plus2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      astep st
        (APlus a1 a2) (APlus a1 a2')
  | AS_Plus : forall st n1 n2,
      astep st
        (APlus (ANum n1) (ANum n2)) (ANum (n1 + n2))

  | AS_Minus1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      astep st
        (AMinus a1 a2) (AMinus a1' a2)
  | AS_Minus2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      astep st
        (AMinus a1 a2) (AMinus a1 a2')
  | AS_Minus : forall st n1 n2,
      astep st
        (AMinus (ANum n1) (ANum n2)) (ANum (n1 - n2))

  | AS_Mult1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      astep st
        (AMult a1 a2) (AMult a1' a2)
  | AS_Mult2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      astep st
        (AMult a1 a2) (AMult a1 a2')
  | AS_Mult : forall st n1 n2,
      astep st
        (AMult (ANum n1) (ANum n2)) (ANum (n1 * n2)).

Inductive bexp_halt: bexp -> Prop :=
  | BH_True : bexp_halt BTrue
  | BH_False : bexp_halt BFalse.

Inductive bstep : state -> bexp -> bexp -> Prop :=

  | BS_Eq1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      bstep st
        (BEq a1 a2) (BEq a1' a2)
  | BS_Eq2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      bstep st
        (BEq a1 a2) (BEq a1 a2')
  | BS_Eq_True : forall st n1 n2,
      n1 = n2 ->
      bstep st
        (BEq (ANum n1) (ANum n2)) BTrue
  | BS_Eq_False : forall st n1 n2,
      n1 <> n2 ->
      bstep st
        (BEq (ANum n1) (ANum n2)) BFalse

  | BS_Le1 : forall st a1 a1' a2,
      astep st
        a1 a1' ->
      bstep st
        (BLe a1 a2) (BLe a1' a2)
  | BS_Le2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astep st
        a2 a2' ->
      bstep st
        (BLe a1 a2) (BLe a1 a2')
  | BS_Le_True : forall st n1 n2,
      n1 <= n2 ->
      bstep st
        (BLe (ANum n1) (ANum n2)) BTrue
  | BS_Le_False : forall st n1 n2,
      n1 > n2 ->
      bstep st
        (BLe (ANum n1) (ANum n2)) BFalse

  | BS_NotStep : forall st b1 b1',
      bstep st
        b1 b1' ->
      bstep st
        (BNot b1) (BNot b1')
  | BS_NotTrue : forall st,
      bstep st
        (BNot BTrue) BFalse
  | BS_NotFalse : forall st,
      bstep st
        (BNot BFalse) BTrue

  | BS_AndStep : forall st b1 b1' b2,
      bstep st
        b1 b1' ->
      bstep st
       (BAnd b1 b2) (BAnd b1' b2)
  | BS_AndTrue : forall st b,
      bstep st
       (BAnd BTrue b) b
  | BS_AndFalse : forall st b,
      bstep st
       (BAnd BFalse b) BFalse.

Section cstep.

Local Open Scope imp.

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st X a a',
      astep st a a' ->
      cstep (CAss X a, st) (CAss X a', st)
  | CS_Ass : forall st1 st2 X n,
      st2 X = n ->
      (forall Y, X <> Y -> st1 Y = st2 Y) ->
      cstep (CAss X (ANum n), st1) (Skip, st2)
  | CS_SeqStep : forall st c1 c1' st' c2,
      cstep (c1, st) (c1', st') ->
      cstep (c1 ;; c2 , st) (c1' ;; c2, st')
  | CS_Seq : forall st c2,
      cstep (Skip ;; c2, st) (c2, st)
  | CS_IfStep : forall st b b' c1 c2,
      bstep st b b' ->
      cstep
        (If b  Then c1 Else c2 EndIf, st)
        (If b'  Then c1 Else c2 EndIf, st)
  | CS_IfTrue : forall st c1 c2,
      cstep (If BTrue Then c1 Else c2 EndIf, st) (c1, st)
  | CS_IfFalse : forall st c1 c2,
      cstep (If BFalse Then c1 Else c2 EndIf, st) (c2, st)
  | CS_While : forall st b c,
      cstep
        (While b Do c EndWhile, st)
        (If b Then (c;; While b Do c EndWhile) Else Skip EndIf, st).

End cstep.

Definition multi_astep (st: state): aexp -> aexp -> Prop := clos_refl_trans (astep st).

Definition multi_bstep (st: state): bexp -> bexp -> Prop := clos_refl_trans (bstep st).

Definition multi_cstep: com * state -> com * state -> Prop := clos_refl_trans cstep.

Module Assertion_S.

Inductive term : Type :=
  | TNum (n : Z)
  | TDenote (a : aexp)
  | TPlus (t1 t2 : term)
  | TMinus (t1 t2 : term)
  | TMult (t1 t2 : term)
  .

Coercion TNum : Z >-> term.

Bind Scope term_scope with term.
Delimit Scope term_scope with term.

Notation "x + y" := (TPlus x y) (at level 50, left associativity) : term_scope.
Notation "x - y" := (TMinus x y) (at level 50, left associativity) : term_scope.
Notation "x * y" := (TMult x y) (at level 40, left associativity) : term_scope.
Notation "{[ a ]}" := (TDenote ((a)%imp)) (at level 30, no associativity) : term_scope.

Inductive Assertion : Type :=
  | DLe (t1 t2 : term)
  | DLt (t1 t2 : term)
  | DEq (t1 t2 : term)
  | DInj (b: bexp)
  | DProp (P: Prop)
  | DOr (d1 d2 : Assertion)
  | DAnd (d1 d2 : Assertion)
  | DNot (d: Assertion)
  | DExists (d: Z -> Assertion)
  | DForall (d: Z -> Assertion).

Coercion DProp : Sortclass >-> Assertion.
Bind Scope assert_scope with Assertion.
Delimit Scope assert_scope with assert.

Notation "x <= y" := (DLe ((x)%term) ((y)%term)) (at level 70, no associativity) : assert_scope.
Notation "x '<' y" := (DLt ((x)%term) ((y)%term)) (at level 70, no associativity) : assert_scope.
Notation "x == y" := (DEq ((x)%term) ((y)%term)) (at level 70, no associativity) : assert_scope.
Notation "{[ b ]}" := (DInj ((b)%imp)) (at level 30, no associativity) : assert_scope.
Notation "x 'OR' y" := (DOr x y) (at level 76, left associativity) : assert_scope.
Notation "x 'AND' y" := (DAnd x y) (at level 74, left associativity) : assert_scope.
Notation "'NOT' x" := (DNot x) (at level 73, right associativity) : assert_scope.
Notation "'EXISTS' x ',' d " := (DExists (fun x: Z => ((d)%assert))) (at level 77, x ident, right associativity) : assert_scope.
Notation "'FORALL' x ',' d " := (DForall (fun x: Z => ((d)%assert))) (at level 77, x ident, right associativity) : assert_scope.

Definition eqb_compute: nat -> nat -> bool :=
  fix eqb (n m : nat) {struct n} : bool :=
  match n with
  | 0%nat => match m with
             | 0%nat => true
             | S _ => false
             end
  | S n' => match m with
            | 0%nat => false
            | S m' => eqb n' m'
            end
  end.

Section subst.

Variable X: var.
Variable a: aexp.

Fixpoint aexp_sub (a0: aexp): aexp :=
    match a0 with
    | ANum n => ANum n
    | AId X' =>
         if eqb_compute X X'
         then a
         else @AId X'
    | APlus a1 a2 => APlus (aexp_sub a1) (aexp_sub a2)
    | AMinus a1 a2 => AMinus (aexp_sub a1) (aexp_sub a2)
    | AMult a1 a2 => AMult (aexp_sub a1) (aexp_sub a2)
    end.

Fixpoint bexp_sub (b: bexp): bexp :=
    match b with
    | BTrue => BTrue
    | BFalse => BFalse
    | BEq a1 a2 => BEq (aexp_sub a1) (aexp_sub a2)
    | BLe a1 a2 => BLe (aexp_sub a1) (aexp_sub a2)
    | BNot b => BNot (bexp_sub b)
    | BAnd b1 b2 => BAnd (bexp_sub b1) (bexp_sub b2)
    end.

Fixpoint term_sub (t: term) :=
    match t with
    | TNum n => TNum n
    | TDenote a => TDenote (aexp_sub a)
    | TPlus t1 t2 => TPlus (term_sub t1) (term_sub t2)
    | TMinus t1 t2 => TMinus (term_sub t1) (term_sub t2)
    | TMult t1 t2 => TMult (term_sub t1) (term_sub t2)
    end.

Fixpoint assn_sub (d: Assertion): Assertion :=
    match d with
    | DLe t1 t2 => DLe (term_sub t1) (term_sub t2)
    | DLt t1 t2 => DLt (term_sub t1) (term_sub t2)
    | DEq t1 t2 => DEq (term_sub t1) (term_sub t2)
    | DInj b => DInj (bexp_sub b)
    | DProp P => DProp P
    | DOr d1 d2 => DOr (assn_sub d1) (assn_sub d2)
    | DAnd d1 d2 => DAnd (assn_sub d1) (assn_sub d2)
    | DNot d => DNot (assn_sub d)
    | DExists d => DExists (fun z: Z => assn_sub (d z))
    | DForall d => DForall (fun z: Z => assn_sub (d z))
    end.

End subst.

Definition aexp_denote (st: state) (a: aexp): Z :=
  aeval a st.

Definition bexp_denote (st: state) (b: bexp): Prop :=
  beval b st.

Fixpoint term_denote (st: state) (t: term): Z :=
  match t with
  | TNum n => n
  | TDenote a => aexp_denote st a
  | TPlus t1 t2 => (term_denote st t1) + (term_denote st t2)
  | TMinus t1 t2 => (term_denote st t1) - (term_denote st t2)
  | TMult t1 t2 => (term_denote st t1) * (term_denote st t2)
  end.

Fixpoint Assertion_denote (st: state) (d: Assertion): Prop :=
  match d with
  | DLe t1 t2 => (term_denote st t1) <= (term_denote st t2)
  | DLt t1 t2 => (term_denote st t1) < (term_denote st t2)
  | DEq t1 t2 => (term_denote st t1) = (term_denote st t2)
  | DInj b => bexp_denote st b
  | DProp P => P
  | DOr d1 d2 => (Assertion_denote st d1) \/ (Assertion_denote st d2)
  | DAnd d1 d2 => (Assertion_denote st d1) /\ (Assertion_denote st d2)
  | DNot d => ~ (Assertion_denote st d)
  | DExists d => exists k, Assertion_denote st (d k)
  | DForall d => forall k, Assertion_denote st (d k)
  end.

Definition derives: Assertion -> Assertion -> Prop :=
  fun d1 d2: Assertion =>
  (forall st, Assertion_denote st d1 -> Assertion_denote st d2).

Opaque derives.

Definition equiv_assert (P Q: Assertion): Prop :=
  derives P Q /\ derives Q P.

Parameter hoare_triple: Assertion -> com -> Assertion -> Prop.

Notation "P '|--' Q" :=
  (derives ((P)%assert) ((Q)%assert)) (at level 90, no associativity).

Notation "P '--||--' Q" :=
  (equiv_assert P Q) (at level 90, no associativity).

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level).

Theorem FOL_complete: forall d1 d2: Assertion,
  (forall st, Assertion_denote st d1 -> Assertion_denote st d2) ->
  d1 |-- d2.
Proof.
  intros.
  exact H.
Qed.

Section simpl.

Fixpoint aexp_simpl (a: aexp): term :=
    match a with
    | ANum n => TNum n
    | AId X => TDenote (AId X)
    | APlus a1 a2 => TPlus (aexp_simpl a1) (aexp_simpl a2)
    | AMinus a1 a2 => TMinus (aexp_simpl a1) (aexp_simpl a2)
    | AMult a1 a2 => TMult (aexp_simpl a1) (aexp_simpl a2)
    end.

Fixpoint bexp_simpl (b: bexp): Assertion :=
    match b with
    | BTrue => DProp True
    | BFalse => DProp False
    | BEq a1 a2 => DEq (aexp_simpl a1) (aexp_simpl a2)
    | BLe a1 a2 => DLe (aexp_simpl a1) (aexp_simpl a2)
    | BNot b => DNot (bexp_simpl b)
    | BAnd b1 b2 => DAnd (bexp_simpl b1) (bexp_simpl b2)
    end.

Fixpoint term_simpl (t: term) :=
    match t with
    | TNum n => TNum n
    | TDenote a => aexp_simpl a
    | TPlus t1 t2 => TPlus (term_simpl t1) (term_simpl t2)
    | TMinus t1 t2 => TMinus (term_simpl t1) (term_simpl t2)
    | TMult t1 t2 => TMult (term_simpl t1) (term_simpl t2)
    end.

Fixpoint assn_simpl (d: Assertion): Assertion :=
    match d with
    | DLe t1 t2 => DLe (term_simpl t1) (term_simpl t2)
    | DLt t1 t2 => DLt (term_simpl t1) (term_simpl t2)
    | DEq t1 t2 => DEq (term_simpl t1) (term_simpl t2)
    | DInj b => bexp_simpl b
    | DProp P => DProp P
    | DOr d1 d2 => DOr (assn_simpl d1) (assn_simpl d2)
    | DAnd d1 d2 => DAnd (assn_simpl d1) (assn_simpl d2)
    | DNot d => DNot (assn_simpl d)
    | DExists d => DExists (fun z: Z => assn_simpl (d z))
    | DForall d => DForall (fun z: Z => assn_simpl (d z))
    end.

Inductive elim_trivial_ex: Assertion -> Assertion -> Prop :=
  | elim_trivial_ex_kernal:
      forall d d': Assertion,
        elim_trivial_ex d d' ->
        elim_trivial_ex (DExists (fun z: Z => d)) d'
  | elim_trivial_ex_ex':
      forall d d': Z -> Assertion,
        (forall z, elim_trivial_ex (d z) (d' z)) ->
        elim_trivial_ex (DExists d) (DExists d')
  | elim_trivial_ex_all':
      forall d d': Z -> Assertion,
        (forall z, elim_trivial_ex (d z) (d' z)) ->
        elim_trivial_ex (DForall d) (DForall d')
  | elim_trivial_ex_or:
      forall d1 d2 d1' d2': Assertion,
        elim_trivial_ex d1 d1' ->
        elim_trivial_ex d2 d2' ->
        elim_trivial_ex (DOr d1 d2) (DOr d1' d2')
  | elim_trivial_ex_and:
      forall d1 d2 d1' d2': Assertion,
        elim_trivial_ex d1 d1' ->
        elim_trivial_ex d2 d2' ->
        elim_trivial_ex (DAnd d1 d2) (DAnd d1' d2')
  | elim_trivial_ex_not:
      forall d d': Assertion,
        elim_trivial_ex d d' ->
        elim_trivial_ex (DNot d) (DNot d')
  | elim_trivial_ex_atom:
      forall d: Assertion,
        elim_trivial_ex d d.

Lemma elim_trivial_ex_ex:
      forall d d': Z -> Assertion,
        (forall z, exists d'', elim_trivial_ex (d z) d'' /\ d'' = d' z) ->
        elim_trivial_ex (DExists d) (DExists d').
Proof.
  intros.
  eapply elim_trivial_ex_ex'.
  intros z; specialize (H z).
  destruct H as [d'' [? ?]].
  subst.
  exact H.
Qed.

Lemma elim_trivial_ex_all:
      forall d d': Z -> Assertion,
        (forall z, exists d'', elim_trivial_ex (d z) d'' /\ d'' = d' z) ->
        elim_trivial_ex (DForall d) (DForall d').
Proof.
  intros.
  eapply elim_trivial_ex_all'.
  intros z; specialize (H z).
  destruct H as [d'' [? ?]].
  subst.
  exact H.
Qed.

End simpl.

Axiom simpl_derives: forall P Q,
  P |-- Q <-> assn_simpl P |-- assn_simpl Q.

Axiom simpl_triple: forall P c Q,
  {{P}} c {{Q}} <-> {{assn_simpl P}} c {{assn_simpl Q}}.

Axiom elim_trivial_ex_derives: forall P Q P' Q',
  elim_trivial_ex P P' -> elim_trivial_ex Q  Q' -> (P |-- Q <-> P' |-- Q').

Axiom elim_trivial_ex_triple: forall P c Q P' Q',
  elim_trivial_ex P P' -> elim_trivial_ex Q  Q' -> ({{P}} c {{Q}} <-> {{P'}} c {{Q'}}).

End Assertion_S.

Module Concrete_Pretty_Printing.
Export Assertion_S.

Class var {var_name: var}: Type :=
  var_name_trivial: var_name = var_name.

Ltac new_var_tac n :=
  first [ try (assert (@var n) by (typeclasses eauto); fail 1);
          exact (eq_refl: @var n); fail 100
        | new_var_tac constr:(S n)].

Notation "'new_var()'" := ltac:(new_var_tac 0%nat).

Definition AId {var_name} (X: @var var_name): aexp := AId var_name.

Coercion AId : var >-> aexp.

Definition CAss {var_name} (v : @var var_name) (a : aexp): com :=
  CAss var_name a.

Notation "x '::=' a" :=
  (CAss x a) (at level 80) : imp_scope.

Definition aexp_sub {var_name} (X: @var var_name) a a0 := aexp_sub var_name a a0.

Definition bexp_sub {var_name} (X: @var var_name) a b := bexp_sub var_name a b.

Definition term_sub {var_name} (X: @var var_name) a t := term_sub var_name a t.

Definition assn_sub {var_name} (X: @var var_name) a d := assn_sub var_name a d.

Arguments aexp_sub {var_name} (X) (a) (a0): simpl never.
Arguments bexp_sub {var_name} (X) (a) (b): simpl never.
Arguments term_sub {var_name} (X) (a) (t): simpl never.
Arguments assn_sub {var_name} (X) (a) (d): simpl never.

Notation "d [ X |-> a ]" := (assn_sub X a ((d)%assert)) (at level 10, X at next level) : assert_scope.
Notation "a0 [ X |-> a ]" := (aexp_sub X a ((a0)%imp)) (at level 10, X at next level) : imp_scope.

Inductive dec: bool -> bool -> Type :=
  | DCEnd (a: Assertion): dec true false
  | DCSeq_A {f1 f2} (a: Assertion) (c: dec f1 f2): dec true f2
  | DCSeq_C {f1 f2} (c1: dcom) (c: dec f1 f2): dec false true

with decorated: Type :=
  | DCBegin (c: dec true true)

with dcom : Type :=
  | DCSkip : dcom
  | DCAss : forall {var_name: nat}, @var var_name -> aexp -> dcom
  | DCIf : bexp -> decorated -> decorated -> dcom
  | DCWhile : bexp -> decorated -> dcom.

Delimit Scope dcom_scope with dcom.
Bind Scope dcom_scope with dcom.
Bind Scope dcom_scope with dec.
Bind Scope dcom_scope with decorated.

Notation "'Skip'" :=
   DCSkip : dcom_scope.
Notation "x '::=' a" :=
  (DCAss x a%imp) (at level 80) : dcom_scope.
Notation "'While' b 'Do' c 'EndWhile'" :=
  (DCWhile b c) (at level 80, right associativity) : dcom_scope.
Notation "'If' c1 'Then' c2 'Else' c3 'EndIf'" :=
  (DCIf c1 c2 c3) (at level 10, right associativity) : dcom_scope.
Notation "c1 '*/' '/*' c2" :=
  (@DCSeq_A true _ c1 c2) (at level 80, right associativity) : dcom_scope.
Notation "c1 ';;' '/*' c2" :=
  (@DCSeq_C true true c1 c2) (at level 80, right associativity) : dcom_scope.
Notation "c1 '/*' c2" :=
  (@DCSeq_C true false c1 c2) (at level 80, right associativity) : dcom_scope.
Notation "c1 '*/' c2" :=
  (@DCSeq_A false _ c1 c2) (at level 80, right associativity) : dcom_scope.
Notation "c1 ';;' c2" :=
  (@DCSeq_C false true c1 c2) (at level 80, right associativity) : dcom_scope.
Notation "c '*/'" := (DCEnd c) (at level 80, right associativity) : dcom_scope.
Notation "'/*' c" := (DCBegin c) (at level 80, right associativity) : dcom_scope.

Module sample_decorated_program.

Local Open Scope dcom_scope.

Local Instance X: var := new_var().
Local Instance Y: var := new_var().

Definition dc1 (m n: Z) : decorated :=
  /* 0 <= m */
  X ::= m;;
  Y ::= 0;;
  /* n * {[Y]} + {[X]} == m AND 0 <= {[X]} */
  While n <= X Do
    /* n * {[Y]} + {[X]} == m AND 0 <= {[X]} AND {[n <= X]} */
    X ::= X - n;;
    Y ::= Y + 1
    /* n * {[Y]} + {[X]} == m AND 0 <= {[X]} */
  EndWhile
  /* n * {[Y]} + {[X]} == m AND 0 <= {[X]} AND NOT {[n <= X]} */
  /* n * {[Y]} + {[X]} == m AND 0 <= {[X]} AND {[X]} < n */.

Definition dc2 (m n: Z) : decorated :=
  /* 0 <= m */
  X ::= m;;
  /* EXISTS x, 0 <= m AND {[X]} == m */
  /* 0 <= m AND {[X]} == m */
  Y ::= 0;;
  /* EXISTS y, 0 <= m AND {[X]} == m AND {[Y]} == 0 */
  /* n * {[Y]} + {[X]} == m AND 0 <= {[X]} */
  While n <= X Do
    /* n * {[Y]} + {[X]} == m AND 0 <= {[X]} AND {[n <= X]} */
    X ::= X - n;;
    /* EXISTS x, n * {[Y]} + {[x]} == m AND 0 <= {[x]} AND
                 {[n <= x]} AND {[X]} == {[x - n]} */
    /* EXISTS x, n * {[Y]} + x == m AND 0 <= x AND
                 n <= x AND {[X]} == x - n */
    /* n * {[Y]} + {[X]} + n == m AND 0 <= {[X]} */
    Y ::= Y + 1
    /* EXISTS y, n * {[y]} + {[X]} + n == m AND 0 <= {[X]} AND
                 {[Y]} == {[y + 1]} */
    /* EXISTS y, n * y + {[X]} + n == m AND 0 <= {[X]} AND
                 {[Y]} == y + 1 */
    /* n * {[Y]} + {[X]} == m AND 0 <= {[X]} */
  EndWhile
  /* n * {[Y]} + {[X]} == m AND 0 <= {[X]} AND NOT {[n <= X]} */
  /* n * {[Y]} + {[X]} == m AND 0 <= {[X]} AND {[X]} < n */.

End sample_decorated_program.

End Concrete_Pretty_Printing.

Module slow_minus.
Section slow_minus.
Import Concrete_Pretty_Printing.

Variables m p: Z.

Instance X: var := new_var().
Instance Y: var := new_var().
Instance Z: var := new_var().
Instance W: var := new_var().
Instance ID: var := new_var().

Definition prog: com :=
    X ::= m;;
    Z ::= p;;
    While !(X == 0) Do
      Z ::= Z - 1;;
      X ::= X - 1
    EndWhile.

Definition prog2: com :=
    X ::= X + Y;;
    Y ::= X - Y;;
    X ::= X - Y.

Definition prog3: com :=
  If X <= Y
  Then Z ::= X - Y
  Else If X <= Y
       Then Skip
       Else Z ::= Y - X
       EndIf
  EndIf.

End slow_minus.
End slow_minus.

Module Assertion_S_Tac.

Export Assertion_S.

Tactic Notation "assert_subst" :=
  unfold Concrete_Pretty_Printing.assn_sub, Concrete_Pretty_Printing.aexp_sub;
  simpl assn_sub;
  simpl aexp_sub;
  repeat match goal with
         | |- context [AId ?var_name] =>
              change (AId ?var_name)
              with (@Concrete_Pretty_Printing.AId var_name _)
             end.

Tactic Notation "assert_subst" "in" constr(H) :=
  unfold Concrete_Pretty_Printing.assn_sub, Concrete_Pretty_Printing.aexp_sub in H;
  simpl assn_sub in H;
  simpl aexp_sub in H;
  repeat match type of H with
         | context [AId ?var_name] =>
              change (AId ?var_name)
              with (@Concrete_Pretty_Printing.AId var_name _) in H
             end.

Ltac assert_simpl_concl :=
  match goal with
  | |- {{ _ }} _ {{ _ }} =>
      rewrite simpl_triple;
      simpl assn_simpl
  | |- _ |-- _ =>
      rewrite simpl_derives;
      simpl assn_simpl
  end;
  repeat match goal with
         | |- context [AId ?var_name] =>
              change (AId ?var_name)
              with (@Concrete_Pretty_Printing.AId var_name _)
             end.

Ltac assert_simpl_assu H :=
  match type of H with
  | {{ _ }} _ {{ _ }} =>
      rewrite simpl_triple in H;
      simpl assn_simpl in H
  | _ |-- _ =>
      rewrite simpl_derives in H;
      simpl assn_simpl in H
  end;
  repeat match type of H with
         | context [AId ?var_name] =>
              change (AId ?var_name)
              with (@Concrete_Pretty_Printing.AId var_name _) in H
             end.

Ltac solve_elim_trivial_ex :=
  idtac;
  first
  [ simple eapply elim_trivial_ex_kernal; solve_elim_trivial_ex
  | simple eapply elim_trivial_ex_ex;
    let x := fresh "x" in intro x;
    eexists; split; [solve_elim_trivial_ex |];
    match goal with
    | |- ?P = _ =>
         let P' := fresh "P" in
         let P' := eval pattern x in P in
         change P with P';
         reflexivity
    end
  | simple eapply elim_trivial_ex_all;
    let x := fresh "x" in intro x;
    eexists; split; [solve_elim_trivial_ex |];
    match goal with
    | |- ?P = _ =>
         let P' := fresh "P" in
         let P' := eval pattern x in P in
         change P with P';
         reflexivity
    end
  | simple apply elim_trivial_ex_or; solve_elim_trivial_ex
  | simple apply elim_trivial_ex_and; solve_elim_trivial_ex
  | simple apply elim_trivial_ex_not; solve_elim_trivial_ex
  | simple apply elim_trivial_ex_atom ].

Ltac elim_trivial_ex_concl :=
  match goal with
  | |- {{ _ }} _ {{ _ }} =>
      erewrite elim_trivial_ex_triple;
      [ | solve_elim_trivial_ex ..]
  | |- _ |-- _ =>
      erewrite elim_trivial_ex_derives;
      [ | solve_elim_trivial_ex ..]
  end.

Ltac elim_trivial_ex_assu H :=
  match type of H with
  | {{ _ }} _ {{ _ }} =>
      erewrite elim_trivial_ex_triple in H;
      [ | solve_elim_trivial_ex ..]
  | _ |-- _ =>
      erewrite elim_trivial_ex_derives in H;
      [ | solve_elim_trivial_ex ..]
  end.

Tactic Notation "assert_simpl" := assert_simpl_concl; elim_trivial_ex_concl.
Tactic Notation "assert_simpl" "in" constr(H) := assert_simpl_assu H; elim_trivial_ex_assu H.

Ltac entailer :=
  match goal with
  | |- _ |-- _ => idtac
  | _ => fail "The proof goal's conclusion is not an assertion derivation."
  end;
  assert_simpl;
  apply FOL_complete;
  let st := fresh "st" in
  intros st;
  cbv [Assertion_denote term_denote];
  repeat
    match goal with
    | |- context [aexp_denote st (Concrete_Pretty_Printing.AId ?X)] =>
           let X' := fresh X "'" in
           set (X' := aexp_denote st (Concrete_Pretty_Printing.AId X));
           clearbody X';
           revert X'
    end;
  first [ clear st | fail 1 "This is not a concrete derivation." ].

End Assertion_S_Tac.

Module Axiomatic_semantics.
Import Concrete_Pretty_Printing.

Axiom hoare_seq : forall (P Q R: Assertion) (c1 c2: com),
  {{P}} c1 {{Q}} ->
  {{Q}} c2 {{R}} ->
  {{P}} c1;;c2 {{R}}.

Axiom hoare_skip : forall P,
  {{P}} Skip {{P}}.

Axiom hoare_if : forall P Q b c1 c2,
  {{ P AND {[b]} }} c1 {{ Q }} ->
  {{ P AND NOT {[b]} }} c2 {{ Q }} ->
  {{ P }} If b Then c1 Else c2 EndIf {{ Q }}.

Axiom hoare_while : forall P b c,
  {{ P AND {[b]} }} c {{P}} ->
  {{P}} While b Do c EndWhile {{ P AND NOT {[b]} }}.

Axiom hoare_asgn_fwd : forall P `(X: var) E,
  {{ P }}
  X ::= E
  {{ EXISTS x, P [X |-> x] AND
               {[X]} == {[ E [X |-> x] ]} }}.

Axiom hoare_consequence : forall (P P' Q Q' : Assertion) c,
  P |-- P' ->
  {{P'}} c {{Q'}} ->
  Q' |-- Q ->
  {{P}} c {{Q}}.

Axiom hoare_asgn_bwd : forall P `(X: var) E,
  {{ P [ X |-> E] }} X ::= E {{ P }}.

End Axiomatic_semantics.

Module Assertion_S_Rules.

Export Assertion_S.

Local Transparent derives.

Lemma AND_left1: forall P Q R: Assertion,
  P |-- R ->
  P AND Q |-- R.
Proof.
  intros.
  intro rho; specialize (H rho).
  simpl.
  tauto.
Qed.

Lemma AND_left2: forall P Q R: Assertion,
  Q |-- R ->
  P AND Q |-- R.
Proof.
  intros.
  intro rho; specialize (H rho).
  simpl.
  tauto.
Qed.

Lemma AND_right: forall P Q R: Assertion,
  P |-- Q ->
  P |-- R ->
  P |-- Q AND R.
Proof.
  intros.
  intro rho; specialize (H rho); specialize (H0 rho).
  simpl.
  tauto.
Qed.

Lemma OR_left: forall P Q R: Assertion,
  P |-- R ->
  Q |-- R ->
  P OR Q |-- R.
Proof.
  intros.
  intro rho; specialize (H rho); specialize (H0 rho).
  simpl.
  tauto.
Qed.

Lemma OR_right1: forall P Q R: Assertion,
  P |-- Q ->
  P |-- Q OR R.
Proof.
  intros.
  intro rho; specialize (H rho).
  simpl.
  tauto.
Qed.

Lemma OR_right2: forall P Q R: Assertion,
  P |-- R ->
  P |-- Q OR R.
Proof.
  intros.
  intro rho; specialize (H rho).
  simpl.
  tauto.
Qed.

Lemma LEM: forall P Q: Assertion,
  P |-- Q OR NOT Q.
Proof.
  intros.
  intro rho.
  simpl.
  tauto.
Qed.

Lemma CONTRA: forall P Q: Assertion,
  P AND NOT P |-- Q.
Proof.
  intros.
  intro rho.
  simpl.
  tauto.
Qed.

Lemma Prop_left: forall (P: Prop) (Q: Assertion),
  ~ P ->
  P |-- Q.
Proof.
  intros.
  intro rho.
  simpl.
  tauto.
Qed.

Lemma Prop_right: forall (P: Assertion) (Q: Prop),
  Q ->
  P |-- Q.
Proof.
  intros.
  intro rho.
  simpl.
  tauto.
Qed.

Lemma False_left: forall (P: Assertion),
  False |-- P.
Proof.
  intros.
  apply Prop_left.
  tauto.
Qed.

Lemma True_right: forall (P: Assertion),
  P |-- True.
Proof.
  intros.
  apply Prop_right.
  tauto.
Qed.

Lemma FORALL_left: forall (P: Z -> Assertion) (Q: Assertion) (x: Z),
  P x |-- Q ->
  FORALL x, P x |-- Q.
Proof.
  intros.
  intro rho.
  simpl.
  firstorder.
Qed.

Lemma FORALL_right: forall (P: Assertion) (Q: Z -> Assertion),
  (forall x, P |-- Q x) ->
  P |-- FORALL x, Q x.
Proof.
  intros.
  intro rho.
  simpl.
  firstorder.
Qed.

Lemma EXISTS_left: forall (P: Z -> Assertion) (Q: Assertion),
  (forall x, P x |-- Q) ->
  EXISTS x, P x |-- Q.
Proof.
  intros.
  intro rho.
  simpl.
  firstorder.
Qed.

Lemma EXISTS_right: forall (P: Assertion) (Q: Z -> Assertion) (x: Z),
  P |-- Q x ->
  P |-- EXISTS x, Q x.
Proof.
  intros.
  intro rho.
  simpl.
  firstorder.
Qed.

Lemma derives_refl: forall (P: Assertion),
  P |-- P.
Proof.
  intros.
  exact (fun rho H => H).
Qed.

Lemma derives_trans: forall (P Q R: Assertion),
  P |-- Q ->
  Q |-- R ->
  P |-- R.
Proof.
  intros.
  exact (fun rho HH => H0 rho (H rho HH)).
Qed.

End Assertion_S_Rules.

Module Assertion_D.
Import Abstract_Pretty_Printing.

Definition logical_var: Type := nat.

Inductive aexp' : Type :=
  | ANum' (t : term)
  | AId' (X: var)
  | APlus' (a1 a2 : aexp')
  | AMinus' (a1 a2 : aexp')
  | AMult' (a1 a2 : aexp')
with term : Type :=
  | TNum (n : Z)
  | TId (x: logical_var)
  | TDenote (a : aexp')
  | TPlus (t1 t2 : term)
  | TMinus (t1 t2 : term)
  | TMult (t1 t2 : term).

Inductive bexp' : Type :=
  | BTrue'
  | BFalse'
  | BEq' (a1 a2 : aexp')
  | BLe' (a1 a2 : aexp')
  | BNot' (b : bexp')
  | BAnd' (b1 b2 : bexp').

Coercion ANum' : term >-> aexp'.
Coercion AId' : var >-> aexp'.
Bind Scope vimp_scope with aexp'.
Bind Scope vimp_scope with bexp'.
Delimit Scope vimp_scope with vimp.

Notation "x + y" := (APlus' x y) (at level 50, left associativity) : vimp_scope.
Notation "x - y" := (AMinus' x y) (at level 50, left associativity) : vimp_scope.
Notation "x * y" := (AMult' x y) (at level 40, left associativity) : vimp_scope.
Notation "x <= y" := (BLe' x y) (at level 70, no associativity) : vimp_scope.
Notation "x == y" := (BEq' x y) (at level 70, no associativity) : vimp_scope.
Notation "x && y" := (BAnd' x y) (at level 40, left associativity) : vimp_scope.
Notation "'!' b" := (BNot' b) (at level 39, right associativity) : vimp_scope.

Coercion TNum : Z >-> term.
Coercion TId: logical_var >-> term.
Bind Scope term_scope with term.
Delimit Scope term_scope with term.

Notation "x + y" := (TPlus x y) (at level 50, left associativity) : term_scope.
Notation "x - y" := (TMinus x y) (at level 50, left associativity) : term_scope.
Notation "x * y" := (TMult x y) (at level 40, left associativity) : term_scope.
Notation "{[ a ]}" := (TDenote ((a)%vimp)) (at level 30, no associativity) : term_scope.

(** Of course, every normal expression is a variable expression. *)

Fixpoint ainj (a: aexp): aexp' :=
  match a with
  | ANum n        => ANum' (TNum n)
  | AId X         => AId' X
  | APlus a1 a2   => APlus' (ainj a1) (ainj a2)
  | AMinus a1 a2  => AMinus' (ainj a1) (ainj a2)
  | AMult a1 a2   => AMult' (ainj a1) (ainj a2)
  end.

Fixpoint binj (b : bexp): bexp' :=
  match b with
  | BTrue       => BTrue'
  | BFalse      => BFalse'
  | BEq a1 a2   => BEq' (ainj a1) (ainj a2)
  | BLe a1 a2   => BLe' (ainj a1) (ainj a2)
  | BNot b1     => BNot' (binj b1)
  | BAnd b1 b2  => BAnd' (binj b1) (binj b2)
  end.

(** The following two lines of [Coercion] definition say that Coq will treat
[a] as [ainj b] and treat [b] a s [binj b] automatically when a variable
expression is needed. *)

Coercion ainj: aexp >-> aexp'.
Coercion binj: bexp >-> bexp'.

Inductive Assertion : Type :=
  | AssnLe (t1 t2 : term)
  | AssnLt (t1 t2 : term)
  | AssnEq (t1 t2 : term)
  | AssnDenote (b: bexp')
  | AssnOr (P1 P2 : Assertion)
  | AssnAnd (P1 P2 : Assertion)
  | AssnImpl (P1 P2 : Assertion)
  | AssnNot (P: Assertion)
  | AssnExists (x: logical_var) (P: Assertion)
  | AssnForall (x: logical_var) (P: Assertion).

Bind Scope assert_scope with Assertion.
Delimit Scope assert_scope with assert.

Notation "x <= y" := (AssnLe ((x)%term) ((y)%term)) (at level 70, no associativity) : assert_scope.
Notation "x '<' y" := (AssnLt ((x)%term) ((y)%term)) (at level 70, no associativity) : assert_scope.
Notation "x == y" := (AssnEq ((x)%term) ((y)%term)) (at level 70, no associativity) : assert_scope.
Notation "{[ b ]}" := (AssnDenote ((b)%vimp)) (at level 30, no associativity) : assert_scope.
Notation "P1 'OR' P2" := (AssnOr P1 P2) (at level 76, left associativity) : assert_scope.
Notation "P1 'AND' P2" := (AssnAnd P1 P2) (at level 74, left associativity) : assert_scope.
Notation "P1 'IMPLY' P2" := (AssnImpl P1 P2) (at level 77, right associativity) : assert_scope.
Notation "'NOT' P" := (AssnNot P) (at level 73, right associativity) : assert_scope.
Notation "'EXISTS' x ',' P " := (AssnExists x ((P)%assert)) (at level 79,  right associativity) : assert_scope.
Notation "'FORALL' x ',' P " := (AssnForall x ((P)%assert)) (at level 79, right associativity) : assert_scope.

Fixpoint aexp_rename (x y: logical_var) (a: aexp'): aexp' :=
    match a with
    | ANum' t => ANum' (term_rename x y t)
    | AId' X => AId' X
    | APlus' a1 a2 => APlus' (aexp_rename x y a1) (aexp_rename x y a2)
    | AMinus' a1 a2 => AMinus' (aexp_rename x y a1) (aexp_rename x y a2)
    | AMult' a1 a2 => AMult' (aexp_rename x y a1) (aexp_rename x y a2)
    end
with term_rename (x y: logical_var) (t: term) :=
    match t with
    | TNum n => TNum n
    | TId x' => 
        if Nat.eq_dec x x'
        then TId y
        else TId x'
    | TDenote a => TDenote (aexp_rename x y a)
    | TPlus t1 t2 => TPlus (term_rename x y t1) (term_rename x y t2)
    | TMinus t1 t2 => TMinus (term_rename x y t1) (term_rename x y t2)
    | TMult t1 t2 => TMult (term_rename x y t1) (term_rename x y t2)
    end.

Fixpoint bexp_rename (x y: logical_var) (b: bexp'): bexp' :=
    match b with
    | BTrue' => BTrue'
    | BFalse' => BFalse'
    | BEq' a1 a2 => BEq' (aexp_rename x y a1) (aexp_rename x y a2)
    | BLe' a1 a2 => BLe' (aexp_rename x y a1) (aexp_rename x y a2)
    | BNot' b => BNot' (bexp_rename x y b)
    | BAnd' b1 b2 => BAnd' (bexp_rename x y b1) (bexp_rename x y b2)
    end.

Fixpoint assn_rename (x y: logical_var) (d: Assertion): Assertion :=
    match d with
    | AssnLe t1 t2    => AssnLe (term_rename x y t1) (term_rename x y t2)
    | AssnLt t1 t2    => AssnLt (term_rename x y t1) (term_rename x y t2)
    | AssnEq t1 t2    => AssnEq (term_rename x y t1) (term_rename x y t2)
    | AssnDenote b    => AssnDenote (bexp_rename x y b)
    | AssnOr P1 P2    => AssnOr (assn_rename x y P1) (assn_rename x y P2)
    | AssnAnd P1 P2   => AssnAnd (assn_rename x y P1) (assn_rename x y P2)
    | AssnImpl P1 P2  => AssnImpl (assn_rename x y P1) (assn_rename x y P2)
    | AssnNot P       => AssnNot (assn_rename x y P)
    | AssnExists x' P => if Nat.eq_dec x x'
                         then AssnExists x' P
                         else AssnExists x' (assn_rename x y P)
    | AssnForall x' P => if Nat.eq_dec x x'
                         then AssnForall x' P
                         else AssnForall x' (assn_rename x y P)
    end.

Fixpoint aexp_max_var (a: aexp'): logical_var :=
    match a with
    | ANum' t => term_max_var t
    | AId' X => O
    | APlus' a1 a2 => max (aexp_max_var a1) (aexp_max_var a2)
    | AMinus' a1 a2 => max (aexp_max_var a1) (aexp_max_var a2)
    | AMult' a1 a2 => max (aexp_max_var a1) (aexp_max_var a2)
    end
with term_max_var (t: term): logical_var :=
    match t with
    | TNum n => O
    | TId x => x
    | TDenote a => aexp_max_var a
    | TPlus t1 t2 => max (term_max_var t1) (term_max_var t2)
    | TMinus t1 t2 => max (term_max_var t1) (term_max_var t2)
    | TMult t1 t2 => max (term_max_var t1) (term_max_var t2)
    end.

Fixpoint bexp_max_var (b: bexp'): logical_var :=
    match b with
    | BTrue' => O
    | BFalse' => O
    | BEq' a1 a2 => max (aexp_max_var a1) (aexp_max_var a2)
    | BLe' a1 a2 => max (aexp_max_var a1) (aexp_max_var a2)
    | BNot' b => bexp_max_var b
    | BAnd' b1 b2 => max (bexp_max_var b1) (bexp_max_var b2)
    end.

Fixpoint assn_max_var (d: Assertion): logical_var :=
    match d with
    | AssnLe t1 t2    => max (term_max_var t1) (term_max_var t2)
    | AssnLt t1 t2    => max (term_max_var t1) (term_max_var t2)
    | AssnEq t1 t2    => max (term_max_var t1) (term_max_var t2)
    | AssnDenote b    => bexp_max_var b
    | AssnOr P1 P2    => max (assn_max_var P1) (assn_max_var P2)
    | AssnAnd P1 P2   => max (assn_max_var P1) (assn_max_var P2)
    | AssnImpl P1 P2  => max (assn_max_var P1) (assn_max_var P2)
    | AssnNot P       => assn_max_var P
    | AssnExists x' P => max x' (assn_max_var P)
    | AssnForall x' P => max x' (assn_max_var P)
    end.

Definition new_var (P: Assertion) (E: aexp'): logical_var :=
  S (max (assn_max_var P) (aexp_max_var E)).

Fixpoint aexp_sub (X: var) (E: aexp') (a: aexp'): aexp' :=
    match a with
    | ANum' t => ANum' (term_sub X E t)
    | AId' X' =>
         if Nat.eq_dec X X'
         then E
         else AId' X'
    | APlus' a1 a2 => APlus' (aexp_sub X E a1) (aexp_sub X E a2)
    | AMinus' a1 a2 => AMinus' (aexp_sub X E a1) (aexp_sub X E a2)
    | AMult' a1 a2 => AMult' (aexp_sub X E a1) (aexp_sub X E a2)
    end
with term_sub (X: var) (E: aexp') (t: term) :=
    match t with
    | TNum n => TNum n
    | TId x => TId x
    | TDenote a => TDenote (aexp_sub X E a)
    | TPlus t1 t2 => TPlus (term_sub X E t1) (term_sub X E t2)
    | TMinus t1 t2 => TMinus (term_sub X E t1) (term_sub X E t2)
    | TMult t1 t2 => TMult (term_sub X E t1) (term_sub X E t2)
    end.

Fixpoint bexp_sub (X: var) (E: aexp') (b: bexp'): bexp' :=
    match b with
    | BTrue' => BTrue'
    | BFalse' => BFalse'
    | BEq' a1 a2 => BEq' (aexp_sub X E a1) (aexp_sub X E a2)
    | BLe' a1 a2 => BLe' (aexp_sub X E a1) (aexp_sub X E a2)
    | BNot' b => BNot' (bexp_sub X E b)
    | BAnd' b1 b2 => BAnd' (bexp_sub X E b1) (bexp_sub X E b2)
    end.

Fixpoint aexp_occur (x: logical_var) (a: aexp'): nat :=
    match a with
    | ANum' t => term_occur x t
    | AId' X => O
    | APlus' a1 a2 => (aexp_occur x a1) + (aexp_occur x a2)
    | AMinus' a1 a2 => (aexp_occur x a1) + (aexp_occur x a2)
    | AMult' a1 a2 => (aexp_occur x a1) + (aexp_occur x a2)
    end
with term_occur (x: logical_var) (t: term): nat :=
    match t with
    | TNum n => O
    | TId x' => if Nat.eq_dec x x' then S O else O
    | TDenote a => aexp_occur x a
    | TPlus t1 t2 => (term_occur x t1) + (term_occur x t2)
    | TMinus t1 t2 => (term_occur x t1) + (term_occur x t2)
    | TMult t1 t2 => (term_occur x t1) + (term_occur x t2)
    end.

Fixpoint bexp_occur (x: logical_var) (b: bexp'): nat :=
    match b with
    | BTrue' => O
    | BFalse' => O
    | BEq' a1 a2 => (aexp_occur x a1) + (aexp_occur x a2)
    | BLe' a1 a2 => (aexp_occur x a1) + (aexp_occur x a2)
    | BNot' b => bexp_occur x b
    | BAnd' b1 b2 => (bexp_occur x b1) + (bexp_occur x b2)
    end.

Fixpoint assn_free_occur (x: logical_var) (d: Assertion): nat :=
    match d with
    | AssnLe t1 t2    => (term_occur x t1) + (term_occur x t2)
    | AssnLt t1 t2    => (term_occur x t1) + (term_occur x t2)
    | AssnEq t1 t2    => (term_occur x t1) + (term_occur x t2)
    | AssnDenote b    => bexp_occur x b
    | AssnOr P1 P2    => (assn_free_occur x P1) + (assn_free_occur x P2)
    | AssnAnd P1 P2   => (assn_free_occur x P1) + (assn_free_occur x P2)
    | AssnImpl P1 P2  => (assn_free_occur x P1) + (assn_free_occur x P2)
    | AssnNot P       => assn_free_occur x P
    | AssnExists x' P => if Nat.eq_dec x x'
                         then O
                         else assn_free_occur x P
    | AssnForall x' P => if Nat.eq_dec x x'
                         then O
                         else assn_free_occur x P
    end.

Fixpoint assn_occur (x: logical_var) (d: Assertion): nat :=
    match d with
    | AssnLe t1 t2    => (term_occur x t1) + (term_occur x t2)
    | AssnLt t1 t2    => (term_occur x t1) + (term_occur x t2)
    | AssnEq t1 t2    => (term_occur x t1) + (term_occur x t2)
    | AssnDenote b    => bexp_occur x b
    | AssnOr P1 P2    => (assn_occur x P1) + (assn_occur x P2)
    | AssnAnd P1 P2   => (assn_occur x P1) + (assn_occur x P2)
    | AssnImpl P1 P2  => (assn_occur x P1) + (assn_occur x P2)
    | AssnNot P       => assn_occur x P
    | AssnExists x' P => if Nat.eq_dec x x'
                         then S (assn_occur x P)
                         else assn_occur x P
    | AssnForall x' P => if Nat.eq_dec x x'
                         then S (assn_occur x P)
                         else assn_occur x P
    end.

Lemma assn_occur_free_occur: forall x P,
  (assn_free_occur x P <= assn_occur x P)%nat.
Proof.
  intros.
  induction P; simpl.
  - apply le_n.
  - apply le_n.
  - apply le_n.
  - apply le_n.
  - apply plus_le_compat; tauto.
  - apply plus_le_compat; tauto.
  - apply plus_le_compat; tauto.
  - exact IHP.
  - destruct (Nat.eq_dec x x0).
    * apply Nat.le_0_l.
    * exact IHP.
  - destruct (Nat.eq_dec x x0).
    * apply Nat.le_0_l.
    * exact IHP.
Qed.

Corollary assn_occur_O: forall x P,
  assn_occur x P = O ->
  assn_free_occur x P = O.
Proof.
  intros.
  pose proof assn_occur_free_occur x P.
  rewrite H in H0.
  inversion H0.
  reflexivity.
Qed.

Fixpoint rename_all (E: aexp') (d: Assertion): Assertion :=
    match d with
    | AssnLe t1 t2   => AssnLe t1 t2
    | AssnLt t1 t2   => AssnLt t1 t2
    | AssnEq t1 t2   => AssnEq t1 t2
    | AssnDenote b   => AssnDenote b
    | AssnOr P1 P2   => AssnOr (rename_all E P1) (rename_all E P2)
    | AssnAnd P1 P2  => AssnAnd (rename_all E P1) (rename_all E P2)
    | AssnImpl P1 P2 => AssnImpl (rename_all E P1) (rename_all E P2)
    | AssnNot P      => AssnNot (rename_all E P)
    | AssnExists x P => match aexp_occur x E with
                        | O => AssnExists x (rename_all E P)
                        | _ => AssnExists
                                 (new_var (rename_all E P) E)
                                 (assn_rename x
                                   (new_var (rename_all E P) E)
                                   (rename_all E P))
                        end
    | AssnForall x P => match aexp_occur x E with
                        | O => AssnForall x (rename_all E P)
                        | _ => AssnForall
                                 (new_var (rename_all E P) E)
                                 (assn_rename x
                                   (new_var (rename_all E P) E)
                                   (rename_all E P))
                        end
    end.

Fixpoint naive_sub (X: var) (E: aexp') (d: Assertion): Assertion :=
    match d with
    | AssnLe t1 t2   => AssnLe (term_sub X E t1) (term_sub X E t2)
    | AssnLt t1 t2   => AssnLt (term_sub X E t1) (term_sub X E t2)
    | AssnEq t1 t2   => AssnEq (term_sub X E t1) (term_sub X E t2)
    | AssnDenote b   => AssnDenote (bexp_sub X E b)
    | AssnOr P1 P2   => AssnOr (naive_sub X E P1) (naive_sub X E P2)
    | AssnAnd P1 P2  => AssnAnd (naive_sub X E P1) (naive_sub X E P2)
    | AssnImpl P1 P2 => AssnImpl (naive_sub X E P1) (naive_sub X E P2)
    | AssnNot P      => AssnNot (naive_sub X E P)
    | AssnExists x P => AssnExists x (naive_sub X E P)
    | AssnForall x P => AssnForall x (naive_sub X E P)
    end.

Definition assn_sub (X: var) (E: aexp') (P: Assertion): Assertion :=
  naive_sub X E (rename_all E P).

Notation "d [ X |-> a ]" := (assn_sub X a ((d)%assert)) (at level 10, X at next level) : assert_scope.
Notation "a0 [ X |-> a ]" := (aexp_sub X a ((a0)%vimp)) (at level 10, X at next level) : vimp_scope.

Inductive hoare_triple: Type :=
| Build_hoare_triple (P: Assertion) (c: com) (Q: Assertion).

Notation "{{ P }}  c  {{ Q }}" :=
  (Build_hoare_triple P c%imp Q) (at level 90, c at next level).

Class FirstOrderLogic: Type := {
  FOL_provable: Assertion -> Prop
}.

Definition derives {T: FirstOrderLogic} (P Q: Assertion): Prop :=
  FOL_provable (P IMPLY Q).

Notation "P '|--' Q" :=
  (derives ((P)%assert) ((Q)%assert)) (at level 90, no associativity).

Inductive provable {T: FirstOrderLogic}: hoare_triple -> Prop :=
  | hoare_seq : forall (P Q R: Assertion) (c1 c2: com),
      provable ({{P}} c1 {{Q}}) ->
      provable ({{Q}} c2 {{R}}) ->
      provable ({{P}} c1;;c2 {{R}})
  | hoare_skip : forall P,
      provable ({{P}} Skip {{P}})
  | hoare_if : forall P Q (b: bexp) c1 c2,
      provable ({{ P AND {[b]} }} c1 {{ Q }}) ->
      provable ({{ P AND NOT {[b]} }} c2 {{ Q }}) ->
      provable ({{ P }} If b Then c1 Else c2 EndIf {{ Q }})
  | hoare_while : forall P (b: bexp) c,
      provable ({{ P AND {[b]} }} c {{P}}) ->
      provable ({{P}} While b Do c EndWhile {{ P AND NOT {[b]} }})
  | hoare_asgn_bwd : forall P (X: var) (E: aexp),
      provable ({{ P [ X |-> E] }} X ::= E {{ P }})
  | hoare_consequence : forall (P P' Q Q' : Assertion) c,
      P |-- P' ->
      provable ({{P'}} c {{Q'}}) ->
      Q' |-- Q ->
      provable ({{P}} c {{Q}}).

Notation "|--  tr" := (provable tr) (at level 91, no associativity).

Definition Lassn: Type := logical_var -> Z.

Definition Lassn_update (La: Lassn) (x: logical_var) (v: Z): Lassn :=
  fun y => if (Nat.eq_dec x y) then v else La y.

Lemma Lassn_update_spec: forall La x v,
  (Lassn_update La x v) x = v /\
  (forall y, x <> y -> La y = (Lassn_update La x v) y).
Proof.
  intros.
  unfold Lassn_update.
  split.
  + destruct (Nat.eq_dec x x).
    - reflexivity.
    - assert (x = x). { reflexivity. }
      tauto.
  + intros.
    destruct (Nat.eq_dec x y).
    - tauto.
    - reflexivity.
Qed.

Definition Interp: Type := state * Lassn.

Definition Interp_Lupdate (J: Interp) (x: logical_var) (v: Z): Interp :=
  (fst J, Lassn_update (snd J) x v).

Fixpoint aexp'_denote (J: Interp) (a: aexp'): Z :=
    match a with
    | ANum' t => term_denote J t
    | AId' X => (fst J) X
    | APlus' a1 a2 => aexp'_denote J a1 + aexp'_denote J a2
    | AMinus' a1 a2 => aexp'_denote J a1 - aexp'_denote J a2
    | AMult' a1 a2 => aexp'_denote J a1 * aexp'_denote J a2
    end
with term_denote (J: Interp) (t: term): Z :=
    match t with
    | TNum n => n
    | TId x => (snd J) x
    | TDenote a => aexp'_denote J a
    | TPlus t1 t2 => term_denote J t1 + term_denote J t2
    | TMinus t1 t2 => term_denote J t1 - term_denote J t2
    | TMult t1 t2 => term_denote J t1 * term_denote J t2
    end.

Fixpoint bexp'_denote (J: Interp) (b: bexp'): Prop :=
    match b with
    | BTrue' => True
    | BFalse' => False
    | BEq' a1 a2 => aexp'_denote J a1 = aexp'_denote J a2
    | BLe' a1 a2 => (aexp'_denote J a1 <= aexp'_denote J a2)%Z
    | BNot' b => ~ bexp'_denote J b
    | BAnd' b1 b2 => bexp'_denote J b1 /\ bexp'_denote J b2
    end.

Fixpoint satisfies (J: Interp) (d: Assertion): Prop :=
    match d with
    | AssnLe t1 t2 => (term_denote J t1 <= term_denote J t2)%Z
    | AssnLt t1 t2 => (term_denote J t1 < term_denote J t2)%Z
    | AssnEq t1 t2 => (term_denote J t1 = term_denote J t2)%Z
    | AssnDenote b => bexp'_denote J b
    | AssnOr P1 P2 => (satisfies J P1) \/ (satisfies J P2)
    | AssnAnd P1 P2 => (satisfies J P1) /\ (satisfies J P2)
    | AssnImpl P1 P2 => ~ (satisfies J P1) \/ (satisfies J P2)
    | AssnNot P => ~ (satisfies J P)
    | AssnExists x P => exists v, satisfies (Interp_Lupdate J x v) P
    | AssnForall x P => forall v, satisfies (Interp_Lupdate J x v) P
    end.

Notation "J  |==  x" := (satisfies J x) (at level 90, no associativity).

Definition valid (Tr: hoare_triple): Prop :=
  match Tr with
  | Build_hoare_triple P c Q =>
      forall La st1 st2,
        (st1, La) |== P -> ceval c st1 st2 -> (st2, La) |== Q
  end.

Notation "|==  Tr" := (valid Tr) (at level 91, no associativity).

Lemma aeval_aexp'_denote: forall st La a,
  aeval a st = aexp'_denote (st, La) (ainj a).
Proof.
  intros.
  induction a; simpl.
  + reflexivity.
  + reflexivity.
  + rewrite IHa1, IHa2.
    reflexivity.
  + rewrite IHa1, IHa2.
    reflexivity.
  + rewrite IHa1, IHa2.
    reflexivity.
Qed.

Lemma beval_bexp'_denote: forall st La b,
  beval b st <-> bexp'_denote (st, La) (binj b).
Proof.
  intros.
  induction b; simpl.
  + tauto.
  + tauto.
  + rewrite <- aeval_aexp'_denote.
    rewrite <- aeval_aexp'_denote.
    tauto.
  + rewrite <- aeval_aexp'_denote.
    rewrite <- aeval_aexp'_denote.
    tauto.
  + tauto.
  + tauto.
Qed.

Record Interp_Equiv (J1 J2: Interp): Prop := {
  state_equiv: forall X: var, fst J1 X = fst J2 X;
  Lassn_equiv: forall x: logical_var, snd J1 x = snd J2 x
}.

Lemma Interp_Equiv_trans: forall J1 J2 J3,
  Interp_Equiv J1 J2 ->
  Interp_Equiv J2 J3 ->
  Interp_Equiv J1 J3.
Proof.
  intros.
  destruct H as [?H ?H].
  destruct H0 as [?H ?H].
  constructor.
  + intros.
    specialize (H X).
    specialize (H0 X).
    rewrite H, H0.
    reflexivity.
  + intros.
    specialize (H1 x).
    specialize (H2 x).
    rewrite H1, H2.
    reflexivity.
Qed.

Lemma Interp_Equiv_sym: forall J1 J2,
  Interp_Equiv J1 J2 ->
  Interp_Equiv J2 J1.
Proof.
  intros.
  destruct H as [?H ?H].
  constructor.
  + intros.
    rewrite H; reflexivity.
  + intros.
    rewrite H0; reflexivity.
Qed.

Lemma Interp_Equiv_Interp_Lupdate: forall J1 J2 x v,
  Interp_Equiv J1 J2 ->
  Interp_Equiv (Interp_Lupdate J1 x v) (Interp_Lupdate J2 x v).
Proof.
  intros.
  apply Build_Interp_Equiv.
  + intros.
    simpl.
    apply state_equiv.
    exact H.
  + intros.
    destruct J1 as [st1 La1], J2 as [st2 La2].
    simpl.
    unfold Lassn_update.
    destruct (Nat.eq_dec x x0).
    - reflexivity.
    - pose proof Lassn_equiv _ _ H.
      simpl in H0.
      apply H0.
Qed.

Lemma Lassn_update_update_self: forall st La x,
  Interp_Equiv
    (st, Lassn_update La x (La x))
    (st, La).
Proof.
  intros.
  apply Build_Interp_Equiv.
  + intros.
    simpl.
    reflexivity.
  + intros.
    simpl.
    unfold Lassn_update.
    destruct (Nat.eq_dec x x0).
    - subst x0;
      reflexivity.
    - reflexivity.
Qed.

Lemma Lassn_update_update_same: forall st La x v1 v2,
  Interp_Equiv
    (st, Lassn_update (Lassn_update La x v1) x v2)
    (st, Lassn_update La x v2).
Proof.
  intros.
  apply Build_Interp_Equiv.
  + intros.
    simpl.
    reflexivity.
  + intros.
    simpl.
    unfold Lassn_update.
    destruct (Nat.eq_dec x x0).
    - reflexivity.
    - reflexivity.
Qed.

Lemma Lassn_update_update_diff: forall st La x1 x2 v1 v2,
  x1 <> x2 ->
  Interp_Equiv
    (st, Lassn_update (Lassn_update La x1 v1) x2 v2)
    (st, Lassn_update (Lassn_update La x2 v2) x1 v1).
Proof.
  intros.
  apply Build_Interp_Equiv.
  + intros.
    simpl.
    reflexivity.
  + intros.
    simpl.
    unfold Lassn_update.
    destruct (Nat.eq_dec x1 x), (Nat.eq_dec x2 x).
    - exfalso.
      apply H; subst; reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
Qed.

Definition state_update (st: state) (X: var) (v: Z): state :=
  fun Y => if (Nat.eq_dec X Y) then v else st Y.

Lemma state_update_spec: forall st X v,
  (state_update st X v) X = v /\
  (forall Y, X <> Y -> st Y = (state_update st X v) Y).
Proof.
  intros.
  unfold state_update.
  split.
  + destruct (Nat.eq_dec X X).
    - reflexivity.
    - assert (X = X). { reflexivity. }
      tauto.
  + intros.
    destruct (Nat.eq_dec X Y).
    - tauto.
    - reflexivity.
Qed.

Lemma state_update_update_same: forall st La X v1 v2,
  Interp_Equiv
    (state_update (state_update st X v1) X v2, La)
    (state_update st X v2, La).
Proof.
  intros.
  apply Build_Interp_Equiv.
  + intros.
    simpl.
    unfold state_update.
    destruct (Nat.eq_dec X X0).
    - reflexivity.
    - reflexivity.
  + intros.
    simpl.
    reflexivity.
Qed.

Lemma state_update_update_diff: forall st La X1 X2 v1 v2,
  X1 <> X2 ->
  Interp_Equiv
    (state_update (state_update st X1 v1) X2 v2, La)
    (state_update (state_update st X2 v2) X1 v1, La).
Proof.
  intros.
  apply Build_Interp_Equiv.
  + intros.
    simpl.
    unfold state_update.
    destruct (Nat.eq_dec X1 X), (Nat.eq_dec X2 X).
    - exfalso.
      apply H; subst; reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  + intros.
    simpl.
    reflexivity.
Qed.

Lemma state_update_update_self: forall st La X,
  Interp_Equiv
    (state_update st X (st X), La)
    (st, La).
Proof.
  intros.
  apply Build_Interp_Equiv.
  + intros.
    simpl.
    unfold state_update.
    destruct (Nat.eq_dec X X0).
    - subst X0;
      reflexivity.
    - reflexivity.
  + intros.
    simpl.
    reflexivity.
Qed.

Lemma aexp'_denote_Interp_Equiv: forall J1 J2 a,
  Interp_Equiv J1 J2 ->
  aexp'_denote J1 a = aexp'_denote J2 a
with term_denote_Interp_Equiv: forall J1 J2 t,
  Interp_Equiv J1 J2 ->
  term_denote J1 t = term_denote J2 t.
Proof.
{
  clear aexp'_denote_Interp_Equiv.
  intros.
  induction a; simpl.
  + apply term_denote_Interp_Equiv.
    exact H.
  + apply state_equiv.
    exact H.
  + rewrite IHa1, IHa2.
    reflexivity.
  + rewrite IHa1, IHa2.
    reflexivity.
  + rewrite IHa1, IHa2.
    reflexivity.
}
{
  clear term_denote_Interp_Equiv.
  intros.
  induction t; simpl.
  + reflexivity.
  + apply Lassn_equiv.
    exact H.
  + apply aexp'_denote_Interp_Equiv.
    exact H.
  + rewrite IHt1, IHt2.
    reflexivity.
  + rewrite IHt1, IHt2.
    reflexivity.
  + rewrite IHt1, IHt2.
    reflexivity.
}
Qed.

Lemma bexp'_denote_Interp_Equiv: forall J1 J2 b,
  Interp_Equiv J1 J2 ->
  (bexp'_denote J1 b <-> bexp'_denote J2 b).
Proof.
  intros.
  induction b; simpl.
  + tauto.
  + tauto.
  + pose proof aexp'_denote_Interp_Equiv _ _ a1 H.
    pose proof aexp'_denote_Interp_Equiv _ _ a2 H.
    rewrite H0, H1.
    tauto.
  + pose proof aexp'_denote_Interp_Equiv _ _ a1 H.
    pose proof aexp'_denote_Interp_Equiv _ _ a2 H.
    rewrite H0, H1.
    tauto.
  + tauto.
  + tauto.
Qed.

Lemma satisfies_Interp_Equiv: forall J1 J2 P,
  Interp_Equiv J1 J2 ->
  (J1 |== P <-> J2 |== P).
Proof.
  intros.
  revert J1 J2 H; induction P; simpl; intros.
  + pose proof term_denote_Interp_Equiv _ _ t1 H.
    pose proof term_denote_Interp_Equiv _ _ t2 H.
    rewrite H0, H1.
    tauto.
  + pose proof term_denote_Interp_Equiv _ _ t1 H.
    pose proof term_denote_Interp_Equiv _ _ t2 H.
    rewrite H0, H1.
    tauto.
  + pose proof term_denote_Interp_Equiv _ _ t1 H.
    pose proof term_denote_Interp_Equiv _ _ t2 H.
    rewrite H0, H1.
    tauto.
  + apply bexp'_denote_Interp_Equiv.
    exact H.
  + specialize (IHP1 _ _ H).
    specialize (IHP2 _ _ H).
    tauto.
  + specialize (IHP1 _ _ H).
    specialize (IHP2 _ _ H).
    tauto.
  + specialize (IHP1 _ _ H).
    specialize (IHP2 _ _ H).
    tauto.
  + specialize (IHP _ _ H).
    tauto.
  + apply Morphisms_Prop.ex_iff_morphism.
    hnf; intros v.
    apply IHP.
    apply Interp_Equiv_Interp_Lupdate.
    exact H.
  + apply Morphisms_Prop.all_iff_morphism.
    hnf; intros v.
    apply IHP.
    apply Interp_Equiv_Interp_Lupdate.
    exact H.
Qed.

End Assertion_D.

Module OneBinRel_FOL.

Definition logical_var: Type := nat.

Inductive term: Type :=
| TId (v: logical_var): term.

Inductive prop: Type :=
| PEq (t1 t2: term): prop
| PRel (t1 t2: term): prop
| PFalse: prop
| PImpl (P Q: prop): prop
| PForall (x: logical_var) (P: prop): prop.

Definition PTrue: prop := PImpl PFalse PFalse.
Definition PNot (P: prop): prop := PImpl P PFalse.
Definition PAnd (P Q: prop): prop := PNot (PImpl P (PNot Q)). 
Definition POr (P Q: prop): prop := PImpl (PNot P) Q. 
Definition PExists (x: logical_var) (P: prop): prop :=
  PNot (PForall x (PNot P)).

Bind Scope FOL_scope with prop.
Delimit Scope FOL_scope with FOL.

Notation "x == y" := (PEq x y) (at level 70, no associativity) : FOL_scope.
Notation "P1 'OR' P2" := (POr P1 P2) (at level 76, left associativity) : FOL_scope.
Notation "P1 'AND' P2" := (PAnd P1 P2) (at level 74, left associativity) : FOL_scope.
Notation "P1 'IMPLY' P2" := (PImpl P1 P2) (at level 77, right associativity) : FOL_scope.
Notation "'NOT' P" := (PNot P) (at level 73, right associativity) : FOL_scope.
Notation "'EXISTS' x ',' P " := (PExists x ((P)%FOL)) (at level 79,  right associativity) : FOL_scope.
Notation "'FORALL' x ',' P " := (PForall x ((P)%FOL)) (at level 79, right associativity) : FOL_scope.

Definition term_rename (x y: logical_var) (t: term) :=
    match t with
    | TId x' => 
        if Nat.eq_dec x x'
        then TId y
        else TId x'
    end.

Fixpoint prop_rename (x y: logical_var) (d: prop): prop :=
    match d with
    | PEq t1 t2    => PEq (term_rename x y t1) (term_rename x y t2)
    | PRel t1 t2   => PRel (term_rename x y t1) (term_rename x y t2)
    | PImpl P1 P2  => PImpl (prop_rename x y P1) (prop_rename x y P2)
    | PFalse       => PFalse
    | PForall x' P => if Nat.eq_dec x x'
                      then PForall x' P
                      else PForall x' (prop_rename x y P)
    end.

Definition term_max_var (t: term): logical_var :=
    match t with
    | TId x => x
    end.

Fixpoint prop_max_var (d: prop): logical_var :=
    match d with
    | PEq t1 t2    => max (term_max_var t1) (term_max_var t2)
    | PRel t1 t2   => max (term_max_var t1) (term_max_var t2)
    | PFalse       => O
    | PImpl P1 P2  => max (prop_max_var P1) (prop_max_var P2)
    | PForall x' P => max x' (prop_max_var P)
    end.

Definition new_var (P: prop) (t: term): logical_var :=
  S (max (prop_max_var P) (term_max_var t)).

Definition term_occur (x: logical_var) (t: term): nat :=
    match t with
    | TId x' => if Nat.eq_dec x x' then S O else O
    end.

Fixpoint prop_free_occur (x: logical_var) (d: prop): nat :=
    match d with
    | PEq t1 t2    => (term_occur x t1) + (term_occur x t2)
    | PRel t1 t2   => (term_occur x t1) + (term_occur x t2)
    | PFalse       => O
    | PImpl P1 P2  => (prop_free_occur x P1) + (prop_free_occur x P2)
    | PForall x' P => if Nat.eq_dec x x'
                      then O
                      else prop_free_occur x P
    end.

Fixpoint rename_all (t: term) (d: prop): prop :=
    match d with
    | PEq t1 t2   => PEq t1 t2
    | PRel t1 t2  => PRel t1 t2
    | PFalse      => PFalse
    | PImpl P1 P2 => PImpl (rename_all t P1) (rename_all t P2)
    | PForall x P => match term_occur x t with
                        | O => PForall x (rename_all t P)
                        | _ => PForall
                                 (new_var (rename_all t P) t)
                                 (prop_rename x
                                   (new_var (rename_all t P) t)
                                   (rename_all t P))
                        end
    end.

Definition term_sub (x: logical_var) (tx: term) (t: term) :=
    match t with
    | TId x' =>
         if Nat.eq_dec x x'
         then tx
         else TId x'
    end.

Fixpoint naive_sub (x: logical_var) (tx: term) (d: prop): prop :=
    match d with
    | PEq t1 t2   => PEq (term_sub x tx t1) (term_sub x tx t2)
    | PRel t1 t2  => PRel (term_sub x tx t1) (term_sub x tx t2)
    | PFalse      => PFalse
    | PImpl P1 P2 => PImpl (naive_sub x tx P1) (naive_sub x tx P2)
    | PForall x P => PForall x (naive_sub x tx P)
    end.

Definition prop_sub (x: logical_var) (tx: term) (P: prop): prop :=
  naive_sub x tx (rename_all tx P).

Notation "P [ x |-> t ]" := (prop_sub x t ((P)%FOL)) (at level 10, x at next level) : FOL_scope.

Inductive provable: prop -> Prop :=
| PImply_1: forall P Q, provable (P IMPLY (Q IMPLY P))
| PImply_2: forall P Q R, provable
   ((P IMPLY Q IMPLY R) IMPLY
    (P IMPLY Q) IMPLY
    (P IMPLY R))
| Modus_ponens: forall P Q,
    provable (P IMPLY Q) ->
    provable P ->
    provable Q
| PFalse_elim: forall P,
    provable (PFalse IMPLY P)
| Excluded_middle: forall P,
    provable (P OR NOT P)
| PForall_elim: forall x t P,
    provable ((FORALL x, P) IMPLY (P [x |-> t]))
| PForall_intros: forall x P Q,
    prop_free_occur x P = O ->
    provable (P IMPLY Q) ->
    provable (P IMPLY FORALL x, Q).

Notation "|--  P" := (provable P) (at level 91, no associativity): FOL_scope.

(** We can formalize its semantics as follows. First, an interpretation is a
domain [D], an interpretation [Rel] of the binary relation symbol [PRel] and
assignments of all logical variables.*)

Inductive Interp: Type :=
| Build_Interp (D: Type) (Rel: D -> D -> Prop) (La: logical_var -> D) : Interp.

Definition domain_of (J: Interp): Type :=
  match J with
  | Build_Interp D _ _ => D
  end.

Definition Rel_of (J: Interp): domain_of J -> domain_of J -> Prop :=
  match J as J0 return
    match J0 with
    | Build_Interp D Rel La => D
    end ->
    match J0 with
    | Build_Interp D Rel La => D
    end ->
    Prop
  with
  | Build_Interp D Rel La => Rel
  end.

Definition Lassn_of (J: Interp): logical_var -> domain_of J :=
  match J as J0 return
    logical_var -> 
    match J0 with
    | Build_Interp D Rel La => D
    end
  with
  | Build_Interp D Rel La => La
  end.

Definition Lassn_update {D: Type} (La: logical_var -> D) (x: logical_var) (v: D): logical_var -> D :=
  fun y => if (Nat.eq_dec x y) then v else La y.

Definition Interp_Lupdate (J: Interp) (x: logical_var): domain_of J -> Interp :=
  match J with
  | Build_Interp D Rel La =>
     fun v => Build_Interp D Rel (Lassn_update La x v)
  end.

Definition term_denote (J: Interp) (t: term): domain_of J :=
    match t with
    | TId x => Lassn_of J x
    end.

Fixpoint satisfies (J: Interp) (d: prop): Prop :=
    match d with
    | PEq t1 t2   => (term_denote J t1 = term_denote J t2)
    | PRel t1 t2  => Rel_of J (term_denote J t1) (term_denote J t2)
    | PFalse      => False
    | PImpl P1 P2 => ~ (satisfies J P1) \/ (satisfies J P2)
    | PForall x P => forall v, satisfies (Interp_Lupdate J x v) P
    end.

Notation "J  |==  x" := (satisfies J x) (at level 90, no associativity): FOL_scope.

Local Open Scope FOL_scope.

Definition valid (P: prop): Prop :=
  forall J: Interp, J |== P.

Notation "|==  P" := (valid P) (at level 91, no associativity): FOL_scope.

Definition sound: Prop :=
  forall P: prop, |-- P -> |== P.

Definition complete: Prop :=
  forall P: prop, |== P -> |-- P.

Lemma prop_sub_spec: forall J (P: prop) (x: logical_var) (t: term),
  J |== P[ x |-> t] <->
  Interp_Lupdate J x (term_denote J t) |== P.
Admitted.

Lemma no_occ_satisfies: forall J P x v,
  prop_free_occur x P = O ->
  (J |== P <-> Interp_Lupdate J x v |== P).
Admitted.

End OneBinRel_FOL.

(* Sat May 4 08:46:51 UTC 2019 *)