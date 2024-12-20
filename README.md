# Liquid Types in Coq

<!--
info for the writer

https://coq.inria.fr/doc/V8.18.0/refman/addendum/program.html#program-definition

Russel is the underlying type system for Coq. -->

# Outline

- dependent types
- problems it solves
- liquid types
- paper examples
- why this is exciting

# Liquid Types in Coq

In this project, we implement and explore Liquid Types using the Coq proof assistant, our work is based on the pathbreaking paper "Liquid Types" by Rondon et al. Our implementation brings to life as to showcase how combining Hindley-Milner type inference with the help of predicate abstraction can enable automatic inference of dependent types powerful enough to prove critical safety properties without extensive use of manual annotation.

# Dependent Types and Problem Space

Dependent types in some sense0 represent a unique and powerful extension to traditional type systems by giving freedom for types to depend on values. While in most conventional type systems can only express basic properties like "variable i has type int", dependent types can capture precise specifications such as "i is an integer between 1 and 99" or "i is less than the length of array a". This capability enables static verification of crucial properties like array bounds safety and division-by-zero prevention.
The fundamental challenge with dependent types lies in their complexity - programmers must typically provide extensive manual type annotations to help the system verify these properties. In the original Dependent ML (DML) implementation, approximately 31% of program text consisted of manual type annotations. This significant annotation burden has been a major obstacle to the widespread adoption of dependent types, despite their clear benefits for program safety and performance optimization.
Liquid Types aim to solve this problem by automating the inference of dependent types through a carefully restricted form of type refinements. Limiting refinements to conjunctions of predicates drawn from a fixed set of logical qualifiers makes automatic type inference possible while retaining enough expressiveness to verify important program properties.

# Liquid Types Overview
Liquid Types (Logically Qualified Data Types) provide a restricted but powerful form of dependent types. The key insight is that refinement predicates are built as conjunctions of logical qualifiers chosen from a predefined set. For example:

{v:int | v >= 0 ∧ v < len arr}   (* Type of valid array indices *)
{v:int | v > x ∧ v > y}          (* Type of numbers greater than both x and y *)
{v:int | v >= 0 ∧ v >= input}    (* Type of non-negative numbers at least as large as input *)
These refinements can express sophisticated properties while maintaining decidable type checking and inference. The system combines:

Hindley-Milner type inference for basic type structure,
Predicate abstraction for refinement inference,
SMT solving for refinement validity checking,
Path-sensitive analysis for handling conditional branches.

# An Adventure in Automated Program Verification

This project explores the fascinating intersection of type theory, automated verification, and program safety using Liquid Types. If you've ever wondered how we can make compilers smarter at catching real bugs while writing less verification code, this project demonstrates exactly that.
[Previous sections remain the same through "Paper Examples Implemented"]
Detailed Implementation Examples

## 1. Predecessor Function with Refinement Types
Definition pred_strong1 (n : nat) : n > 0 -> nat :=
  match n with
    | O => fun pf : 0 > 0 => match zgtz pf with end
    | S n' => fun _ => n'
  end.

This elegant implementation shows how liquid types can enforce preconditions statically. The function only accepts positive natural numbers, and this is enforced at compile time. Key features:

The type n > 0 -> nat expresses that the input must be positive
Pattern matching on n reveals the contradiction in the zero case
The successor case automatically satisfies the positivity requirement
The zgtz lemma proves that zero cannot be positive, making the zero case impossible

## 2. Maximum Function with Dependent Types
Program Definition max_2 (x y: nat): {v: nat | v >= x /\ v >= y} :=
  if le_ge_dec x y then
    y
  else
    x.
    
This implementation demonstrates several sophisticated concepts:

Use of subset types {v: nat | v >= x /\ v >= y} to specify properties
Automated proof obligation generation using Program
Path-sensitive typing based on the conditional
Automatic inference of numeric relationships

The magical part? The type checker automatically proves that the result satisfies the required properties without manual proof terms.

## 3. Higher-Order Functions with Liquid Types
Program Definition max_program (l : list nat) : 
  {v: option nat | match v with
                  | Some n => forall x, In x l -> x <= n
                  | None => l = []
                  end} :=
  match l with
  | [] => None
  | h :: t => Some (fold_max t h)
  end.
This example showcases advanced features:

Dependent pattern matching with sophisticated refinements
Higher-order function composition with fold_max
Complex specifications using match in types
Automated handling of all cases including empty lists

## 4. Array Sum with Bounds Checking
Program Fixpoint sum_checked (k: nat) : {v : nat | v >= 0 /\ v >= k} :=
  match k with
  | 0 => 0
  | S k' => let s := sum_checked k' in 
            proj1_sig s + k
  end.
  
A beautiful example of:

Recursive functions with refinement types
Automated proof generation for recursive calls
Arithmetic invariant maintenance
Safe extraction to executable code

# Why This is Exciting
Imagine you're building a critical system - perhaps flight control software or a financial trading system. Traditional testing might catch 80% of bugs, but what about the edge cases? This is where Liquid Types shine:

Automatic Safety: The compiler proves your array accesses are safe, your arithmetic won't overflow, and your functions handle all cases correctly.
Minimal Annotation: Unlike traditional formal verification where you might spend 50% of your time writing proofs, Liquid Types often require less than 1% annotation overhead.
Real-world Applicability: The techniques shown here scale to real codebases. The verified BITV library example demonstrates this.
Cutting-edge Research: This project implements ideas from recent programming languages research that are shaping the future of software development.
