(** Remark. Some material in this lecture is from << Software Foundation >>
volume 1 and volume 2. *)

Require Import Coq.Lists.List.
Require Import AB.Imp6.

(* ################################################################# *)
(** * Review: Denotations *)

Module Expression_Denotation.

Fixpoint aeval (a : aexp) (st : state) : Z :=
  match a with
  | ANum n => n
  | AId X => st X
  | APlus a1 a2 => (aeval a1 st) + (aeval a2 st)
  | AMinus a1 a2  => (aeval a1 st) - (aeval a2 st)
  | AMult a1 a2 => (aeval a1 st) * (aeval a2 st)
  end.

Fixpoint beval (b : bexp) (st : state) : Prop :=
  match b with
  | BTrue       => True
  | BFalse      => False
  | BEq a1 a2   => (aeval a1 st) = (aeval a2 st)
  | BLe a1 a2   => (aeval a1 st) <= (aeval a2 st)
  | BNot b1     => ~ (beval b1 st)
  | BAnd b1 b2  => (beval b1 st) /\ (beval b2 st)
  end.

End Expression_Denotation.

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

Module Command_Denotation_With_Steps.

Import Expression_Denotation.

(** This time, a program's denotation is defined as a trinary relation.
Specifically, [st1, t, st2] belongs to the denotation of program [c] if and
only if executing [c] from [st1] may take time [t] and stop at state [st2]. *)

Definition skip_sem: state -> Z -> state -> Prop :=
  fun st1 t st2 =>
    st1 = st2 /\ t = 0.

Definition asgn_sem (X: var) (E: aexp): state -> Z -> state -> Prop :=
  fun st1 t st2 =>
    st2 X = aeval E st1 /\
    forall Y, X <> Y -> st1 Y = st2 Y /\
    t = 1.

(** Here we assume every assignment command takes one unit of time. We can
write a more realistic definition here so that different assignment commands
may take different amount of time. *)

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
    (d1 st1 (t - 1) st2 /\ beval b st1) \/
    (d2 st1 (t - 1) st2 /\ ~beval b st1).

(** Here we assume that testing an if-condition will take one unit of time. *)

Fixpoint iter_loop_body
  (b: bexp)
  (loop_body: state -> Z -> state -> Prop)
  (n: nat)
  : state -> Z -> state -> Prop
:=
  match n with
  | O =>
     fun st1 t st2 =>
       (st1 = st2 /\ t = 1) /\ ~beval b st1
  | S n' =>
     fun st1 t st3 =>
       (exists t1 t2 st2,
         (loop_body) st1 t1 st2 /\
         (iter_loop_body b loop_body n') st2 t2 st3 /\
         t = t1 + t2) /\
       beval b st1
  end.

(** Here we assume that testing a loop condition will take one unit of time. *)

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

End Command_Denotation_With_Steps.

Module Denotation_With_Asymptotic_Bound.

(*

forall n, ceval st(n) t st'(n) == T(n) = t

T = O(f) == exists a, N, forall n, n > N -> 0 < T(n) <= f(n)

forall n, {{P(n)}} c {{Q(n)}} O(f(n))

*)

(*
{{P(n)}} Skip {{P(n)}} O(1)

{{P}} X ::= E {{Q}} O(1)

P(n) |- P'(n) ->
{{P'(n)}} c {{Q'(n)}} O(f(n)) ->
Q'(n) |- Q(n) ->
{{P(n)}} c {{Q(n)}} O(f(n))

{{P(n)}} c1 {{Q(n)}} O(f(n)) ->
{{Q(n)}} c2 {{R(n)}} O(g(n)) ->
{{P(n)}} c1;;c2 {{R(n)}} O((f+g)(n))

{{P(n) AND [[b]]}} c1 {{Q(n)}} O(f(n)) ->
{{P(n) AND NOT [[b]]}} c2 {{Q(n)}} O(f(n)) ->
{{P(n)}} If b Then c1 Else c2 EndIf {{Q(n)}} O(f(n)).

{{P(n) AND V(n) AND [[b]]}} c {{P(n) AND V(n')}} O(f(n)) ->
O(g(n)) satisfy T(n) = T(n') + O(f(n)) ->
{{P(n) AND V(n)}} While b Do c EndWhile {{P(n) AND V(0) AND NOT [[b]]}} O(g(n))
*)

End Denotation_With_Asymptotic_Bound.
