Require Import Coq.Arith.Arith.

Definition max (x y: nat): {v: nat | v >= x /\ v >= y}.
  refine (
    if le_ge_dec x y 
    then exist _ y _
    else exist _ x _
  ).
  - split; auto.
  - split. auto. assumption.
Defined.

Compute (max 4 6).

Definition max_val x y := proj1_sig (max x y).

Definition max_proof x y := proj2_sig (max x y).



Compute (max 3 4).

(* To get just the value part *)
Compute (proj1_sig (max 3 4)).

Compute (proj2_sig (max 3 4)).


Compute (max_val 3 4).

(* You can also do test cases *)
Example test_max_1: max_val 3 4 = 4.
Proof. reflexivity. Qed.

Example test_max_2: max_val 5 2 = 5.
Proof. reflexivity. Qed.

