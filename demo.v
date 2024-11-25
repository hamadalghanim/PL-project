Require Import Coq.Arith.Arith.
Require Import Lia.
(** * Demo: Liquid Types in Coq

    This demo illustrates the use of subset types in Coq as Liquid Types.
    For more detailed information, refer to Adam Chlipala's book, "Certified Programming with Dependent Types" available at:
    http://adam.chlipala.net/cpdt/html/Subset.html

    ** What are Liquid Types? 
    
    Liquid Types enrich existing type systems with logical predicates and let you specify and automatically verify semantic properties of your code.

    for example, what if you want the compiler to ensure that a function returns a value within a specific range
    lets take the `index_of` function in js. this function should never return a value that is larger than the length of the array.
    in liquid types that looks like the following:
    [{v:nat | len a > v}]
    To achieve this in coq we have to rely on the subset type, which is a way to restrict a value using some proposition.
    usually written as such [{v: nat | v >= x /\ v >= y}]
    In this demo we will discuss our methodology approaching Liquid Types in Coq.
    ** First Attempt
    Our first attempt to define a max function using subset type
*)

Definition max_not_working (x y: nat): {v: nat | v >= x /\ v >= y}.
  refine (
    if x <? y
    then exist _ y _
    else exist _ x _
  ).
Admitted.
(** 
    As we can see above, the code does not compile because the comparison operator `<?` defined as a [sumbool].
    We need to use the [le_ge_dec] function instead.
    ** Second Attempt
    In this attempt, we will use the `le_ge_dec` function to compare the two numbers.
    which is defined as the following:
    [{n <= m} + {n >= m}]
    which allows us to use both [{n <= m}] & [{n >= m}] in our proofs.
**)

Definition max (x y: nat): {v: nat | v >= x /\ v >= y}.
  refine (
    if le_ge_dec x y
    then exist _ y _
    else exist _ x _
  ).
  lia.
  lia.
Defined.
(** 
    as we can above, the definition is still looking a little bit weird since
    we need to use the `refine` tactic to define the subset type, and then we need to use `exists` to define the value.
    however by doing this we can for now grab the value of the function using 
 **)
Compute proj1_sig (max 1 2).
(** 
  And we can grab the "proof" of this spefic function using

**)
Compute proj2_sig (max 1 2).

(**
  However, trying to define a more complex function such as `sum_k` as a fixpoint we start facing some complexity.
**)
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
(** 
  As we can see above, definiting a simple fixpoint requires some heavy type juggling just to make it work.
  Reading more about tactics in coq we found the [Program] tactic.
  https://coq.inria.fr/doc/V8.18.0/refman/addendum/program.html#program-definition
  ** Third Attempt
  In this attempt, we will use the [Program] tactic to define the sum_k function.
  and we will see how it simplifies the definition of functions/fixpoints with subset type in Coq.
   **)

Program Fixpoint sum_k_program (k: nat) : {v : nat | v >= 0 /\ v >= k} :=
  match k with
  | 0 => 0
  | S k' => let s := sum_k_program k' in 
            proj1_sig s + k
  end.
Next Obligation.
lia.
Defined.

(** Even max function is easier to define using program tactic **)

Program Definition max_2  (x y: nat): {v: nat | v >= x /\ v >= y}:=
  if le_ge_dec x y then
    y
  else
    x.

(**
  ** How does the [Program] tactic work?
  underlying the [Program] tactic is a type checker that checks the correctness of the program.
  Named Russel https://sozeau.gitlabpages.inria.fr/www/research/russell.en.html. 
  The type checker is able to infer the type of the program and check if it is correct. and in some cases
  doesnt even require us to prove something like the max_2 function.
**)

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
Example test_max_1:proj1_sig( max_2 3 4) = 4.
Proof. reflexivity. Qed.

(** 
  Even the proof generated from [proj2_sig] is easier to read
**)