Require Import AB.Imp9.
Require Import AB.PolyAB.

Module Hoare_Logic.
Import Assertion_D.
Import Abstract_Pretty_Printing.
Export Polynomial_Asympotitic_Bound.

Open Scope list_scope.

Inductive hoare_triple: Type :=
| Build_hoare_triple (P: Assertion) (c: com) (Q: Assertion) (AB : AsymptoticBound).

(* Time is defines how costly a program is, thus we use the symbol "$" to state the time comlexity *)
Notation "{{ P }}  c  {{ Q }}  $ T " :=
  (Build_hoare_triple P c%imp Q T) (at level 90, c at next level).

Inductive provable {F: FirstOrderLogic}: hoare_triple -> Prop :=
(** Skip has Constant time complexity. *)
  | hoare_skip : forall (P : Assertion) (n : logical_var),
      provable ({{P}} Skip {{P}} $ BigTheta CONSTANT n)
(** Assignment has Constant time complexity. *)
  | hoare_asgn_bwd : forall (P : Assertion) (X : var) (E : aexp) (n : logical_var),
      provable ({{ P [ X |-> E] }} X ::= E {{ P }} $ BigTheta CONSTANT n)
(**
  The time complexity of Sequenced Command is the sum of time complexity for separate commands in the sense of Big Theta.
*)
  | hoare_seq_bigtheta : forall (P Q R: Assertion) (c1 c2: com) (p1 p2 : poly) (n : logical_var),
      provable ({{P}} c1 {{Q}} $ BigTheta p1 n) ->
      provable ({{Q}} c2 {{R}} $ BigTheta p2 n) ->
      provable ({{P}} c1;;c2 {{R}} $ BigTheta (p1 +++ p2) n)
(**
  The time complexity of If Command is the same as those of its branches, if the time complexity of branch commands are the same.
*)
  | hoare_if_same : forall (P Q : Assertion) (b : bexp) (c1 c2 : com) (T : AsymptoticBound),
      provable ({{ P AND {[b]} }} c1 {{ Q }} $ T) ->
      provable ({{ P AND NOT {[b]} }} c2 {{ Q }} $ T) ->
      provable ({{ P }} If b Then c1 Else c2 EndIf {{ Q }} $ T)
(**
  We can relax the time complexity of certain command to equivalent bounds based on the loosen relation.
*)
  | hoare_loosen : forall (P Q : Assertion) (c : com) (T1 T2 : AsymptoticBound),
      T1 =< T2 ->
      provable ({{P}} c {{Q}} $ T1) ->
      provable ({{P}} c {{Q}} $ T2)
(**
  If the loop variant decrease linearly, by multiplying a linear term onto the asymptotic bound for the inner command, we get the time complexity for the whole loop.
  There are other conditions to be satisfied:
  1) (forall st La, ((st, La) |== (P AND {[b]})) -> ((st, La) |== (0 < V))):
      Loop invariant and the trueness of loop condition imply the status of loop variant.
  2) assn_occur n P = O /\ term_occur n V = O /\ bexp_occur n b = O:
      The logical variable bound to loop variant does not occur in other parts of the pre-condition.
  3) (forall x, 0 < x -> 0 <= poly_eval p x):
      The time cost is non-negative when input size is positive.
  4) (forall x y, x <= y -> poly_eval p x <= poly_eval p y):
      The time cost increases as input size increase.
*)
  | hoare_while_linear : forall (T: FirstOrderLogic) P (b : bexp) (V : term) (n : logical_var) (C : Z) c p,
    (forall st La, ((st, La) |== (P AND {[b]})) -> ((st, La) |== (0 < V))) ->
    assn_occur n P = O ->
    term_occur n V = O ->
    bexp_occur n b = O ->
    0 < C ->
    (forall x, 0 < x -> 0 <= poly_eval p x) ->
    (forall x y, x <= y -> poly_eval p x <= poly_eval p y) ->
    provable ({{P AND {[b]} AND V == n}} c {{P AND V == n-C}} $ BigO p n) ->
    provable ({{P AND V == n }} While b Do c EndWhile {{ P AND NOT {[b]} }} $ BigO (LINEAR *** p) n)
(** Consequence rule holds for the Hoare logic, if time complexity stays unchanged *)
  | hoare_consequence : forall (P P' Q Q' : Assertion) c (T : AsymptoticBound),
      P |-- P' ->
      provable ({{P'}} c {{Q'}} $ T) ->
      Q' |-- Q ->
      provable ({{P}} c {{Q}} $ T).

Notation "|--  tr" := (provable tr) (at level 91, no associativity).

(**
  Following excluded_middle rule comes from the completeness of FOL, since we are not sure how to describe the completeness of FOL properly. It is used once in soundness proof, and is used repeatedly in the proofs of demos.
*)
Axiom excluded_middle : forall P, ~ P \/ P.

End Hoare_Logic.
