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
- written in coq without program
- with program
- conclusion and link to repo

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

Hindley-Milner type inference for basic type structure
Predicate abstraction for refinement inference
SMT solving for refinement validity checking
Path-sensitive analysis for handling conditional branches
