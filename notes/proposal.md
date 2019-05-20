# Proposal: Asymptotic Complexity in Hoare Logic and Denotational Semantics
Team members: Wang Zhongye, Zhan Xinyu
***
## Main Goal
- Introduce the concept of asymptotic complexity into the proof system defined by Hoare Logic and based on Denotational Semantics.

## Sub Goals
- Define various __asymptotic bounds__ and __asymptotic notations__ in coq. It should not be very hard to define bounds within the domain of nature numbers, but would be challenging to expand this into the domain of real numbers. More specifically, _how to include roots and logarithm?_
- __Update the toy language__ to include _list_. (Not sure whether this is necessary or not.)
- Define the __asymptotic complexity with respect to denotational semantics__ by utilizing and upgrading the existing _step counting semantic_.
- Adapt Hoare logic to include __the proof system for asymptotic complexity__.
- Prove __the soundness of Hoare logic__, both the basic Hoare logic and the proof system for asymptotic complexity.
- Prove __the correctness and asymptotic complexity for some simple algorithms__ using what we will build. Possible candidates are as follows:
  - Simple examples we have encountered in class, e.g. slow addition, min while. (Simple.)
  - Identifying Distinct Elements: double-loop, xor. (This is the mini-project of Wang Zhongye. Not very hard but require extended toy language.)
  - Sort Algorithms: selection sort, merge sort. (This is quite challenging, especially the merge sort where logarithmic asymptotic complexity occurs. The selection sort is preferred because it is insensitive to the input.)

## Constraints
There are several constraints that might limit what we can do or simplify what we want to do.
- We do not consider programs with __control statements__, i.e. _break_ and _continue_. Moreover, we do not wish to alter the potential path of program execution in similar ways, which makes the execution time almost independent with the __distribution of input data__. This cause us unable to verify the asymptotic complexity of algorithms like Quick Sort, but will simplify our definition of what is Asymptotic Complexity.
- We will use the __the toy language developed in class__ or the adapted version of it, which only contains very fundamental operations and statements. This will limit the scope of programs and algorithms we can take into consideration.
