Require Import AB.Imp8.
Require Import AB.PolyAB.

Module Hoare_Logic.

Import Assertion_D.
Import Abstract_Pretty_Printing.
Export Polynomial_Asympotitic_Bound.


Inductive hoare_triple: Type :=
| Build_hoare_triple (P: Assertion) (c: com) (Q: Assertion) (AB : AsymptoticBound).

Notation "{{ P }}  c  {{ Q }} $ T " :=
  (Build_hoare_triple P c%imp Q T) (at level 90, c at next level).

(* Provable, should be modified as new hoare rules are added
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
*)

End Hoare_Logic.
