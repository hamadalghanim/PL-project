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

Definition max_val {x y: nat} := 
  proj1_sig (max x y).

Definition max_proof {x y: nat} := 
  proj2_sig (max x y).

Compute (max 3 4).

(* To get just the value part *)
Compute (proj1_sig (max 3 4)).

Compute (proj2_sig (max 3 4)).