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

Inductive provable {T: FirstOrderLogic}: hoare_triple -> Prop :=
  | hoare_seq_bigtheta : forall (P Q R: Assertion) (c1 c2: com) (p1 p2 : poly) (n : logical_var),
      provable ({{P}} c1 {{Q}} $ BigTheta p1 n) ->
      provable ({{Q}} c2 {{R}} $ BigTheta p2 n) ->
      provable ({{P}} c1;;c2 {{R}} $ BigTheta (poly_add p1 p2) n)
  | hoare_while_bigo : forall P V (b: bexp) c (tp f p : poly) (v n : logical_var),
      provable ({{ P AND {[b]} AND V==v }} c {{P AND V==(poly_eval_lv tp v)}} $ BigO f v) ->
      (* solving recursive equation *)
      provable ({{P AND V==n}} While b Do c EndWhile {{ P AND NOT {[b]} }} $ BigO p n)
.

Notation "|--  tr" := (provable tr) (at level 91, no associativity).

End Hoare_Logic.
(*
Module Axiomantic_Semantics.
Export Assertion_S.
Export Polynomial_Asympotitic_Bound.

Parameter hoare_triple : Assertion -> com -> Assertion -> AsymptoticBound -> Prop.

Notation "{{ P }}  c  {{ Q }} $ T " :=
  (hoare_triple P c%imp Q T) (at level 90, c at next level).

Axiom hoare_seq_bigtheta : forall (P Q R : Assertion) (c1 c2 : com) (p1 p2 : poly),
  exists (n : logical_var), {{P}} c1 {{Q}} $ BigTheta p1 n ->
                            {{Q}} c2 {{R}} $ BigTheta p2 n ->
                            {{P}} c1;;c2 {{Q}} $ BigTheta (poly_add p1 p2) n.

End Axiomantic_Semantics.
*)
