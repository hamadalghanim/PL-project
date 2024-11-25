(* Using Program - lets you write the computational part first 
   and then prove the properties separately *)
   (* https://coq.inria.fr/doc/V8.18.0/refman/addendum/program.html *)
Require Import Program.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.


Fixpoint fold_max (l: list nat) (init: nat) : nat :=
  match l with
  | [] => init
  | x :: xs => fold_max xs (Nat.max init x)
  end.
Lemma fold_max_init_le : forall l init,
  init <= fold_max l init.
Proof.
  induction l; simpl; intros.
  - apply Nat.le_refl.
  - apply Nat.le_trans with (Nat.max init a).
  + apply Nat.le_max_l.
  + apply IHl.
Qed.
Lemma fold_max_spec : forall l init x,
  In x l -> x <= fold_max l init.
Proof.
  induction l; simpl; intros.
  - contradiction.
  - destruct H.
  + subst. (* now x = a *)
    apply Nat.le_trans with (Nat.max init x).
    * apply Nat.le_max_r.
    * apply fold_max_init_le.
  + apply (IHl (Nat.max init a) _ H).
Qed.
Program Definition max_program (l : list nat) : 
  {v: option nat | match v with
                  | Some n => forall x, In x l -> x <= n
                  | None => l = []
                  end} :=
  match l with
  | [] => None
  | h :: t => Some (fold_max t h)
  end.
Next Obligation.
    destruct H.
    + subst. apply fold_max_init_le.
    + apply fold_max_spec. assumption.
Qed.


Print max_program.
Compute proj1_sig (max_program []).
Compute proj2_sig (max_program [1;2]).
Compute proj2_sig (max_program []).


(* Using refine - lets you mix computation and proofs more flexibly *)
Definition max_refine (l : list nat) : 
  {v: option nat | match v with
                  | Some n => forall x, In x l -> x <= n
                  | None => l = []
                  end}.
Proof.
  refine (
    match l with
    | [] => exist _ None _
    | h :: t => exist _ (Some (fold_max t h)) _
    end
  ).
  - reflexivity.
  - intros x H. destruct H.
    + subst. apply fold_max_init_le.
    + apply (fold_max_spec t h x H).
Defined.

Print max_refine.

Compute proj1_sig (max_refine [1;2;3;4;5]).
Compute proj1_sig (max_refine []).
Compute proj1_sig (max_refine [42]).

Definition max_refine_proof := proj2_sig (max_refine [1;2;3]).

Print max_refine_proof.
(* Using the proof part *)
Lemma test_max_refine : 
  forall x, In x [1;2;3] -> 
  match proj1_sig (max_refine [1;2;3]) with
  | Some n => x <= n
  | None => False
  end.
Proof.
  intros x H.
  apply (max_refine_proof x H).
Qed.