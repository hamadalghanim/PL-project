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

Definition max (l : list nat) : {v: option nat | match v with
                                               | Some n => forall x, In x l -> x <= n
                                               | None => l = []
                                               end}.
Proof.
  destruct l as [|h t].
  - exists None. reflexivity.
  - exists (Some (fold_max t h)).
    intros x H.
    destruct H as [H|H].
    + subst x. apply fold_max_init_le.
    + apply (fold_max_spec t h x H).
Defined.

(* Get just the value *)
Definition get_max (l: list nat) : option nat := 
  proj1_sig (max l).

(* Get just the proof *)
Definition get_max_proof (l: list nat) : 
  match proj1_sig (max l) with
  | Some n => forall x, In x l -> x <= n
  | None => l = []
  end := proj2_sig (max l).

(* Now we can test easily *)
Example test1: get_max [1;2;3] = Some 3.
Proof. reflexivity. Qed.

Example test2: get_max [] = None.
Proof. reflexivity. Qed.

(* Test the proof part *)
Example test3: forall x, 
  In x [1;2;3] -> 
  x <= match get_max [1;2;3] with
       | Some n => n
       | None => 0  (* arbitrary since this case won't happen *)
       end.
Proof.
  intros x H.
  apply (get_max_proof [1;2;3] x H).
Qed.



