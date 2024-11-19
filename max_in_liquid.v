Require Import Coq.Arith.Arith.
Require Import Notations.
Require Import Lia.
(* http://adam.chlipala.net/cpdt/html/Subset.html *)
(* Definition le_ge_dec n m : {n <= m} + {n >= m}. *)
(* 

Inductive sumbool (A B : Prop) : Set :=
| left : A -> { A } + { B }
| right : B -> { A } + { B }.

so the notation is either A or B holds
using normal Nat.le wont work because there wont be an assumption in our proof

 *)
Locate le_ge_dec.
Print le_ge_dec.
Definition less_than_or_eq n m : {n <= m} + {n >= m}.
  intros; elim (le_lt_dec n m); auto with arith.
Defined.



Definition max (x y: nat): {v: nat | v >= x /\ v >= y}.
  refine (
    if le_ge_dec x y
    then exist _ y _
    else exist _ x _
  ).
  lia. lia.
Defined.

Program Definition max_2  (x y: nat): {v: nat | v >= x /\ v >= y}:=
  if le_ge_dec x y then
    y
  else
    x.

Compute (proj1_sig (max_2 3 4)).
Compute (proj2_sig (max_2 3 4)).

Example test_max_1:proj1_sig( max_2 3 4) = 4.
Proof. reflexivity. Qed.




Compute (max 4 6).

Definition max_val x y := proj1_sig (max x y).

Definition max_proof x y := proj2_sig (max x y).

Print max_proof.


(* To get just the value part *)
Compute (proj1_sig (max 3 4)).

Compute (proj2_sig (max 3 4)).


Compute (max_val 3 4).

(* You can also do test cases *)
Example test_max_1: max_val 3 4 = 4.
Proof. reflexivity. Qed.

Example test_max_2: max_val 5 2 = 5.
Proof. reflexivity. Qed.

