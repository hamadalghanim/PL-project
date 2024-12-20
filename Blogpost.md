# A Study of Liquid Types in Coq

One of the problems that plague programmers is that they, at times, get confused on how to write "Correct Code", in which case some people will recommend the usage of TTD (Test Driven Development) but testing for every edge case is not feasible. Enter Liquid Types. Liquid Types are systems based on types capable of expressing predicates that can be checks at compile time. Consider the function `abs` that gives the absolute value of a number. This way, with Liquid Types, we specify that the result is non-negative, and we are sure that `abs` is correct without testing anything.

```coq
Definition abs (n : Z) : { v : Z | v >= 0 } :=
  if n >=? 0 then n else -n.
```

Let us breakdown the type of the function `abs`. The type `{ v : Z | v >= 0 }` says that the result of the function is a real number `v` such that `v >= 0`. That is to say, `abs` always returns a positive number.

In this blog post, we will learn about the inner working of Coq and how we can implement such a thing with the current tools available in Coq.

## Introduction

Let me start by introducing what Coq is, and then why a programmer would be interested in it. Coq is a proof assistant built on top of Calculus of Construction. Some typical places where Coq plays-in are formal verification, formal methods, and research about programming languages. It's just this nice tool that allows you to check whether your code has any bugs or not.

## Liquid Types

As an introduction to Liquid Types we recommend reading through the original paper [Liquid Types](https://goto.ucsd.edu/~rjhala/liquid/liquid_types.pdf) as it provides a good basis for the topic we are discussing in an academic manner. In the paper, We read through examples such as refining the output of function from the type `Nat` by adding the predicate `v > 0` resulting in `{ v : nat | v > 0 }` this type describes a value of a natrual number with the restriction of it being positive. The UCSD team also published an introductory blog post called [A Gentle Introduction to Liquid Types](https://goto.ucsd.edu/~ucsdpl-blog/liquidtypes/2015/09/19/liquid-types/) that gives a good overview of the concept.

But to tackle such a problem in Coq, we need to refer to adam chipala's work on [Certified Programming with Dependent Types](https://adam.chlipala.net/cpdt/). Reading through Adam's book we see that the best tool to implement Liquid Types in Coq is to use [Subsets](http://adam.chlipala.net/cpdt/html/Subset.html).

## Experiments

As part of our project, we have experimented and iterated on using subset types as we learn more about Coq and its intricacies, below are the experiments we have conducted.

### Experiment 1: Defining a `Max` function with Liquid Types

First, we implemented a simple max function returning a value guaranteed to be greater or equal than both of its inputs. This is what we tried :

```coq
Definition max_not_working (x y: nat): {v: nat | v >= x /\ v >= y}.
  refine (
    if x <? y
    then exist _ y _
    else exist _ x _
  ).
Admitted.
```

The problem with using `<?` is that it just gives us a boolean value (true or false), but doesn't provide Coq with any proof about how the numbers are related. What we really need is `le_ge_dec`, which returns a `sumbool` type - meaning it not only compares the numbers but also provides mathematical proof of their relationship.

### Experiment 2: Fixing our `Max` function

For our second attempt, we used the `le_ge_dec` function, which is defined as `{n <= m} + {n >= m}`. As discussed above, this gives us access to both inequalities in our proof so we can use them to define a working `max` function with Liquid Types:

```coq
Definition max (x y: nat): {v: nat | v >= x /\ v >= y}.
  refine (
    if le_ge_dec x y
    then exist _ y _
    else exist _ x _
  ).
  lia.
  lia.
Defined.
```

We can extract both the computed value and its proof by using the `proj1_sig` and `proj2_sig` functions:

```coq
Compute proj1_sig (max 1 2).  (* Returns the value 2 *)
Compute proj2_sig (max 1 2).  (* Returns the proof *)
```

### Experiment 3: Defining a Recursive `Sum` Function w/Liquid Types

Our next experiment was to define a recursive function that computes the sum of the first `k` natural numbers. We wanted to ensure that the output of the function is always greater than or equal to `k` as this was the example discussed in the paper. Here's one of our attempts:

```coq
Fixpoint sum_k (k: nat) : {v : nat | v >= 0 /\ v >= k}.
  refine (
    match k as n return (n = k -> {v : nat | v >= 0 /\ v >= n}) with
  | 0 => fun _ => exist _ 0 _
  | S k' => fun H => exist _ (proj1_sig (sum_k k') + k) _
  end eq_refl
).
- lia.
- lia.
Defined.

Compute proj1_sig (sum_k 5).
Compute proj2_sig (sum_k 5).
```

This works, However as we can see the type juggling required here is considerable. Dealing with such definitions can get hectic and very cumbersome, why not look for a tool in Coq that can help us simplify the definition of functions with subset types.

### Experiment 4: Using `Program` Tactic to Simplify Subset Definitions

In this attempt, we will use the `Program` tactic to define the sum_k function. and we will see how it simplifies the definition of functions/Fixpoints with subset type in Coq.

```coq
Program Fixpoint sum_k_program (k: nat) : {v : nat | v >= 0 /\ v >= k} :=
  match k with
  | 0 => 0
  | S k' => let s := sum_k_program k' in
             s + k
  end.
Next Obligation.
lia.
Defined.
```

So, What is `Program` and why does it simplify the definition of functions with subset types in Coq?

Underlying the [Program](https://coq.inria.fr/doc/v8.9/refman/addendum/program.html) tactic is the Coq type checker. Named [Russel](https://sozeau.gitlabpages.inria.fr/www/research/russell.en.html).

> The goal of Program is to program as in a regular functional programming language whilst using as rich a specification as desired and proving that the code meets the specification using the whole Coq proof apparatus. This is done using a technique originating from the “Predicate subtyping” mechanism of PVS [ROS98], which generates type checking conditions while typing a term constrained to a particular type.
>
> &mdash; [Coq Reference Manual](https://coq.inria.fr/doc/v8.9/refman/addendum/program.html)

We can also try the program tactic with the `max` function and see how it simplifies the definition of the function.

```coq
Program Definition max_2 (x y: nat): {v: nat | v >= x /\ v >= y} :=
  if le_ge_dec x y then y else x.
```

We did not even need to provide the proof for the function, the program tactic inferred the proof for us.

```coq

Compute (proj1_sig (max_2 3 4)).
(**
    [[
    = 4
    ]]
*)
Compute (proj2_sig (max_2 3 4)).
(**
    [[
     = conj
        (match Nat.succ_le_mono 2 3 with
        | conj x _ => x
        end
          (match Nat.succ_le_mono 1 2 with
          | conj x _ => x
          end (match Nat.succ_le_mono 0 1 with
            | conj x _ => x
            end (Nat.le_0_l 1)))) (le_n 4)      : proj1_sig (max_2 3 4) >= 3 /\
                                                  proj1_sig (max_2 3 4) >= 4
    ]]
**)
Example test_max_1:proj1_sig(max_2 3 4) = 4.
Proof. reflexivity. Qed.
```

Even the proof generated from `proj2_sig` is easier to read.

### Experiment 5: More Examples From The Liquid Types Paper

We can also try to implement the examples from the Liquid Types paper in Coq. Here is an example from the paper that defines a function `foldn` where the function passed is of type `{v : nat | 0 <= v /\ v < n}  -> A -> A` which means we can also use liquid types to specify the properties of functions passed as arguments.

```coq
Program Fixpoint foldn {A: Type } (n : nat) (i : A) (b : A) (f : {v : nat | 0 <= v /\ v < n}  -> A -> A):  A :=
  match n with
  | 0 => b
  | S n' => foldn n' (f n' i) b f
  end.
Next Obligation.
lia.
Defined.
```

We can now use this to define `array_max` function that returns the maximum element of an array, using also liquid types.

```coq
Program Definition arraymax (a: list nat) : {v: nat | v >= 0} :=
  let am l m := max_2 (nth l a 0) m
    in foldn (length a) (length a) 0 am.
Next Obligation.
lia.
Defined.
```

## Conclusion

In this post, we showed how subset types in Coq could be used in order to define Liquid Types. Also exploring the usage of `Program` tactic which is useful when it comes to simplify the definition of functions using subset types.

## Future Work

In the future, we want to investigate more interesting examples of Liquid Types in Coq involving Maps or Integrating it with `Imp`. We will also investigate creating an LTac tactic which can aid in simplifying definitions of functions using `Program` and the subset type, investigate weather adding such a tactic to the core solver of Coq could automate solving the `Obligations `. We hope this post provided you with a good introduction to Liquid Types in Coq and how those could be used in order to verify correctness of your code.

For more information, You can find the readme file for our project linked here: [Liquid Types in Coq](https://github.com/hamadalghanim/PL-project)
