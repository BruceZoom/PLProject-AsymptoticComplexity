# PL-Project: Asymptotic Complexity
The project for programming language course. The main goal of the project is to introduce the concept of asymptotic complexity into the proof system defined by Hoare Logic and based on Denotational Semantics.

___First two sections are almost the same as the proposal, and you may skip to third section directly.___

## __Project Goals__
- [x] Define __polynomial__ to support operations and simplifications in asymptotic bounds.
- [x] Define various __asymptotic bounds__ and __asymptotic notations__ in coq.
- [x] Update __denotational semantics__ to include time step (done in class) and to fit our project.
- Adapt Hoare logic to include __the proof system for asymptotic complexity__.
  - [x] Hoare Skip
  - [x] Hoare Assignment
  - [x] Hoare Sequence BigTheta
  - [ ] Hoare Sequence BigO
  - [ ] Hoare Sequence BigOmega
  - [x] Hoare If Same
  - [x] Hoare Loosen (New Rule)
  - [x] Hoare While Linear
  - [ ] Hoare While General
- Prove __the soundness of Hoare logic__, both the basic Hoare logic and the proof system for asymptotic complexity.
  - [x] Hoare Skip
  - [x] Hoare Assignment
  - [x] Hoare Sequence BigTheta
  - [ ] Hoare Sequence BigO
  - [ ] Hoare Sequence BigOmega
  - [x] Hoare If Same
  - [ ] Hoare Loosen (New Rule)
  - [ ] Hoare While Linear
  - [ ] Hoare While General
- Prove __the correctness and asymptotic complexity for some simple algorithms__ encountered in class using what we will build.
  - [ ] Slow Addition
  - [ ] Min While

## __Constraints__
There are several constraints that might limit what we can do or simplify what we want to do.
- We do not consider programs with __control statements__, i.e. _break_ and _continue_. Moreover, we do not wish to alter the potential path of program execution in similar ways, which makes the execution time almost independent with the __distribution of input data__. This cause us unable to verify the asymptotic complexity of algorithms like Quick Sort, but will simplify our definition of what is Asymptotic Complexity.
- We will use the __the toy language developed in class__ or the adapted version of it, which only contains very fundamental operations and statements. This will limit the scope of programs and algorithms we can take into consideration.

---

## __Project Overview__
Our project has following files:
- __Imp8.v__: basic library of the toy language, from the course.
- __PolyAB.v__: defines polynomial and its operation, and asymptotic bounds defined on polynomials, and mathematic lemmas used later.
- __Denotation.v__: the denational semantics with steps, mainly from the course but modified.
- __HoareLogic.v__: the hoare logic with asymptotic bound, should contain rules and provable definition
- __Soundness.v__: the proof for the soundness of hoare logic
- __Demos.v__: examples of programs proved (or to be proved) using our hoare logic
- __AsymptoticBound.v__: pure mathematic asymptotic bound definition attempts (abandonded)

## __Compilation Order__
Please compile the project in the following order:
- Imp8.v -> PolyAB.v -> Denotation.v -> HoareLogic.v -> Soundness.v -> Demos.v

## __Definitions__
### __Polynomial__ (in PolyAB.v)
- __poly__ (at ___line 11___)
  - A list of Z, each represents a coefficient at certain term.
  - The power increases as the index goes up.
- __poly_eval__ (at ___line 21___)
  - A recursive function that evaluates a poly into functions that maps Z to Z based on the semantics.
- TPower: (at line 31)
  - An auxiliary recursive function that implements the power operation for logical_var.
- __poly_eval_lv__ (at ___line 37___)
  - A recursive function that evaluates a poly into functions that maps logical_var to term based on the semantics. 
  - Might be used in defining recursive equations in Hoare While General Rule.
- __poly_add__ (p1 +++ p2) (at ___line 48___)
  - A recursive function that adds two polys into one poly. 
- __trim_0__ (at ___line 56___)
  - A recursive function that removes 0s at tail, i.e. in the highest order terms. 
  - Used in determining the valid highest order term.
- __poly_scalar_mult__ (k ** p) (at ___line 65___)
  - A recursive function that multiplies a Z scalar to a poly to get a new poly. 
- __poly_mult__ (p1 *** p2) (at ___line 71___)
  - A recursive function that multiplies two polys to get a new poly. 
### __Polynomial Asymptotic Bound__ (in PolyAB.v)
- __AsymptoticBound__ (at ___line 321___)
  - An inductive type that specifies different asymptotic bounds. 
- __ab_eval__ (at ___line 326___)
  - A function that takes Lassn, AsymptoticBound, and other Z parameters to formalize the asymptotic property defined by the asymptotic bound in Porp. 
- __loosen__ (T1 =< T2) (at ___line 338___)
  - An inductive relation that specifies the loosening relationship between two bounds. 
  - The first AB (T1) can be relaxed to the second AB (T2). 
  - We did not prove the correctness in this file, but in the soundness proof of the Hoare Logic.
### __Command Denotation With Steps__ (in Denotation.v)
- skip_sem (at ___line 8___)
  - Almost the same as the one in class, but we specify the time step for Skip to be 1. 
- asgn_sem (at ___line 14___)
  - Almost the same as the one in class, but we move the time step property outside. 
- seq_sem (at line 20)
  - The same as the one in class. 
- if_sem (at line 27)
  - The same as the one in class. 
- loop_sem (at line 53)
  - The same as the one in class. 
- ceval (at line 59)
  - The same as the one in class. 
### __Hoare Logic__ (in HoareLogic.v)
- __hoare_triple__ ({{ P }}  c  {{ Q }}  $ T) (at ___line 11___)
  - An inductive type that specifies the hoare triple.
  - Almost the same as the one in class, but with extra asymptotic bound added. 
- __provable__ (|-- tr) (at ___line 17___)
  - An inductive relation that specifies the Hoare Logic. 
### __Soundness__ (in Soundness.v)
- __valid__ (|== tr) (at ___line 13___)
  - A function that maps hoare_triple to Prop which specifies the validity of Hoare Rules. 

## __Important Theorems__
### __Polynomial__ (in PolyAB.v)
There are many properties about _poly_ we have proven to support later use of it, but the following 4 theorems are the most important ones.
- __poly_add_spec__ (at ___line 170___)
  - Stating that the evaluation of poly_add result is correct.
- __poly_scalar_mult_spec__ (at ___line 182___)
  - Stating that the evaluation of poly_scalar_mult result is correct.
- __poly_mult_spec__ (at ___line 191___)
  - Stating that the evaluation of poly_mult result is correct.
- __trim_invar__ (at ___line 205___)
  - Stating that after trimming redundant 0s, the evaluation is the same as before.

### __Denotation__ (in Denotation.v)
- __command_cost_time__ (at ___line 68___)
  - Stating that any command would cost at least 1 time step.
  - Apply to the denotational semantics, where Skip also cost 1 time step.
  - This property is important in proving the hoare_if_same_soundness, because previously having Skip inside if statement would invalidate that rule, since unfolding if also takes time.

### __Soundness__ (in Soundness.v)
All the Hoare Rules contain the part we have declared in class, thus we will not mention those again.
- hoare_skip_sound (at ___line 27___)
  - Stating that Skip has Constant time complexity.
- hoare_asgn_bwd_sound (at ___line 68___)
  - Stating that Assignment has Constant time complexity.
- __hoare_seq_bigtheta_sound__ (at ___line 96___)
  - Stating that the time complexity of Sequenced Command is the __sum__ of time complexity for separate commands in the sense of Big Theta.
- __hoare_if_same_sound__ (at ___line 166___)
  - Stating that the time complexity of If Command is the __same__ as those of its branches, if the time complexity of branch commands are the same.
- __hoare_loosen_sound__ (at ___line 307___)
  - Stating that we can __relax__ the time complexity of certain command based on the _loosen_ relation.
  - Auxiliary properties about _poly_ is required to prove the loosening rule for asymptotic bounds that have the same highest order.
- __hoare_while_linear__ (at ___line 354___)
  - Stating that if the loop variant decrease linearly, by __multiplying__ a linear term onto the asymptotic bound for the inner command, we get the time complexity for the whole loop.
  - We have just reached the stage to come up with Hoare While Rules, thus this rule requires certain revision and generalization.
- hoare_logic_sound (at ___line 361___)
  - Stating that if a Hoare Triple is provable, then it is valid.

### __Demos__ (in Demos.v)
- __slow_addition_correct__ (at ___line 13___)
  - This example comes from the Exercise 2 of Task 2 in Assignment 2.
  - We want to prove that its time complexity is $\Theta(m)$.
- __min_while_correct__ (at ___line 33___)
  - This example comes from the Exercise 3 of Task 4 in Assignment 2.
  - We want to prove that its time complexity is $O(\min(a, b))$.
  - Since we try to prove something that is not a polynomial, a minimum function, using polynomial asymptotic bound, we might get stuck and might change this to something simpler.
