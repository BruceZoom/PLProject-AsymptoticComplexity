(** (This following part of this file is copied from <<Software Foundation>>
volume 1. It should be only used for lecture notes and homework assignments for
course CS263 of Shanghai Jiao Tong University, 2019 spring. Any other usage are
not allowed. For the material of thses parts, please refer to the original
book.) *)

Require Export ZArith.
Require Export String.
Require Export Classical.

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

Module Abstract_Pretty_Printing.
Coercion AId: var >-> aexp.
End Abstract_Pretty_Printing.

Module Concrete_Pretty_Printing.

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

Definition state: Type := nat -> Z.

Fixpoint aeval (st : state) (a : aexp) : Z :=
  match a with
  | ANum n => n
  | AId X => st X
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : Prop :=
  match b with
  | BTrue       => True
  | BFalse      => False
  | BEq a1 a2   => (aeval st a1) = (aeval st a2)
  | BLe a1 a2   => (aeval st a1) <= (aeval st a2)
  | BNot b1     => ~ (beval st b1)
  | BAnd b1 b2  => (beval st b1) /\ (beval st b2)
  end.

Arguments aeval st a: simpl never.
Arguments beval st b: simpl never.

Fixpoint term_denote (st: state) (t: term): Z :=
  match t with
  | TNum n => n
  | TDenote a => aeval st a
  | TPlus t1 t2 => (term_denote st t1) + (term_denote st t2)
  | TMinus t1 t2 => (term_denote st t1) - (term_denote st t2)
  | TMult t1 t2 => (term_denote st t1) * (term_denote st t2)
  end.

Fixpoint Assertion_denote (st: state) (d: Assertion): Prop :=
  match d with
  | DLe t1 t2 => (term_denote st t1) <= (term_denote st t2)
  | DLt t1 t2 => (term_denote st t1) < (term_denote st t2)
  | DEq t1 t2 => (term_denote st t1) = (term_denote st t2)
  | DInj b => beval st b
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
    | |- context [aeval st (Concrete_Pretty_Printing.AId ?X)] =>
           let X' := fresh X "'" in
           set (X' := aeval st (Concrete_Pretty_Printing.AId X));
           clearbody X';
           revert X'
    end;
  first [ clear st | fail 1 "This is not a concrete derivation." ].

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

Module Assertion_derivation.

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

End Assertion_derivation.

Export Assertion_derivation.

(* Mon Mar 25 15:21:55 UTC 2019 *)