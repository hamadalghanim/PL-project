Require Extraction.
Require Lia.
Require Import Nat.
Extraction Nat.pred.
Lemma zgtz : 0 > 0 -> False.
Proof.
  intros H.              (* Introduce the hypothesis H : 0 > 0 *)
  apply Nat.nlt_0_r in H. (* Use the fact that 0 is not greater than itself *)
  exact H.               (* Conclude by showing the contradiction *)
Qed.

Definition pred_strong1 (n : nat) : n > 0 -> nat :=
  match n with
    | O => fun pf : 0 > 0 => match zgtz pf with end
    | S n' => fun _ => n'
  end.