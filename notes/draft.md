## Overview
```
// concrete computation time definition
forall n, ceval st(n) t st'(n) -> T(n) = t

// asymptotic time bound for denotational semantics
exists a, N, forall n, n > N -> 0 < T(n) <= f(n) -> T = O(f)

// asymptotic time bound for hoare logic (syntax)
forall n, {{P(n)}} c {{Q(n)}} O(f(n))
```
## Hoare logic with asymptotic bound
```
// skip rule is the same
{{P(n)}} Skip {{P(n)}} O(1)

// assignment rules are the same
{{P}} X ::= E {{Q}} O(1)

// consequence rules are the same
P(n) |- P'(n) ->
{{P'(n)}} c {{Q'(n)}} O(f(n)) ->
Q'(n) |- Q(n) ->
{{P(n)}} c {{Q(n)}} O(f(n))

// sequence rule accumulates time
{{P(n)}} c1 {{Q(n)}} O(f(n)) ->
{{Q(n)}} c2 {{R(n)}} O(g(n)) ->
{{P(n)}} c1;;c2 {{R(n)}} O((f+g)(n))

// if rule only supports branches with same time bound
{{P(n) AND [[b]]}} c1 {{Q(n)}} O(f(n)) ->
{{P(n) AND NOT [[b]]}} c2 {{Q(n)}} O(f(n)) ->
{{P(n)}} If b Then c1 Else c2 EndIf {{Q(n)}} O(f(n)).

// while rule
// V stands for statements about loop variant
{{P(n) AND V(n) AND [[b]]}} c {{P(n) AND V(n')}} O(f(n)) ->
O(g(n)) satisfy T(n) = T(n') + O(f(n)) ->
{{P(n) AND V(n)}} While b Do c EndWhile {{P(n) AND V(0) AND NOT [[b]]}} O(g(n))
```

## Problems with Hoare While Linear
Not matter what we use, logical_var or Z, in loop body to specify the change of loop variant, there exists following problem:
- if we put the introduction of $v$ at the most front of the theorem, the property of loop body become too strong to be applied to the second step during induction.
- if we put the introduction of $v$ in the property of loop body, we are unable to extract any information about a1, a2, N.
