Require Import AB.Imp8.
Require Import AB.PolyAB.

Module Hoare_Logic.
Import Assertion_D.
Import Abstract_Pretty_Printing.
Export Polynomial_Asympotitic_Bound.

Open Scope list_scope.

Inductive hoare_triple: Type :=
| Build_hoare_triple (P: Assertion) (c: com) (Q: Assertion) (AB : AsymptoticBound).

Notation "{{ P }}  c  {{ Q }}  $ T " :=
  (Build_hoare_triple P c%imp Q T) (at level 90, c at next level).

Inductive provable {F: FirstOrderLogic}: hoare_triple -> Prop :=
  | hoare_skip : forall (P : Assertion) (n : logical_var),
      provable ({{P}} Skip {{P}} $ BigTheta (1::nil) n)
  | hoare_asgn_bwd : forall (P : Assertion) (X : var) (E : aexp) (n : logical_var),
      provable ({{ P [ X |-> E] }} X ::= E {{ P }} $ BigTheta (1::nil) n)
  | hoare_seq_bigtheta : forall (P Q R: Assertion) (c1 c2: com) (p1 p2 : poly) (n : logical_var),
      provable ({{P}} c1 {{Q}} $ BigTheta p1 n) ->
      provable ({{Q}} c2 {{R}} $ BigTheta p2 n) ->
      provable ({{P}} c1;;c2 {{R}} $ BigTheta (poly_add p1 p2) n)
  | hoare_if_same : forall (P Q : Assertion) (b : bexp) (c1 c2 : com) (T : AsymptoticBound),
      provable ({{ P AND {[b]} }} c1 {{ Q }} $ T) ->
      provable ({{ P AND NOT {[b]} }} c2 {{ Q }} $ T) ->
      provable ({{ P }} If b Then c1 Else c2 EndIf {{ Q }} $ T)
  | hoare_loosen : forall (P Q : Assertion) (c : com) (T1 T2 : AsymptoticBound),
      T1 =< T2 ->
      provable ({{P}} c {{Q}} $ T1) ->
      provable ({{P}} c {{Q}} $ T2)
  | hoare_while_linear : forall (P : Assertion) (b : bexp) (V : term) (n m : logical_var) (C : term) (c : com) (p : poly),
      provable ({{ P AND {[b]} AND V==n }} c {{P AND V==n-C}} $ BigO p n) ->
      provable ({{P AND V==m }} While b Do c EndWhile {{ P AND NOT {[b]} AND V==0 }} $ BigO (poly_mult (1::0::nil) p) m)
  (* This is quite general and difficult to prove, we might consider this when easy cases are cleared
  | hoare_while_bigo : forall P V (b: bexp) c (tp f p : poly) (v n : logical_var),
      provable ({{ P AND {[b]} AND V==v }} c {{P AND V==(poly_eval_lv tp v)}} $ BigO f v) ->
      (* solving recursive equation *)
      provable ({{P AND V==n}} While b Do c EndWhile {{ P AND NOT {[b]} }} $ BigO p n)
  *)
.

Notation "|--  tr" := (provable tr) (at level 91, no associativity).

End Hoare_Logic.
