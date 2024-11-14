(* 

    liquid types are a subset of dependent types that are decidable.
    they can be 
    v <= {}
    v > {}
    v = {}
    v != {} 
    v < len {}
 *)
Require Import Program.
Require Import Lia.
Program Fixpoint sum_checked (k: nat) : {v : nat | v >= 0 /\ v >= k} :=
  match k with
  | 0 => 0
  | S k' => let s := sum_checked k' in 
            proj1_sig s + k
  end.
Next Obligation.
lia.
Defined.


Compute (proj1_sig (sum_checked 5)).
Compute (proj2_sig (sum_checked 3)).

Example test_sum_1: proj1_sig (sum_checked 3) = 6.
Proof. reflexivity. Qed.