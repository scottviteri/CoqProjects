Set Warnings "-notation-overridden,-parsing".
Require Export Tactics.

Check 3 = 3.
Check forall n m : nat, n + m = m + n.
Check 2 = 2.
Check forall n : nat, n = 2.
Check 3 = 4.

Theorem plus_2_2_is_4 : 2 + 2 = 4.
Proof. reflexivity. Qed.

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true : plus_fact.
Proof. reflexivity. Qed.

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.

Definition injective {A B} (f : A -> B) :=
  forall (x y : A), f x = f y -> (x = y).
Check injective.

Check eq.
Check @eq.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof. split; reflexivity. Qed.

Lemma and_intro : 
  forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. 
  split. { apply HA. } { apply HB. }
Qed.

Check and_intro.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro; reflexivity. 
Qed.

Example and_exercise : 
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H. rewrite plus_comm in H. 
  apply and_intro; 
  destruct m in H. { simpl in H. apply H. }
  { inversion H. }

(* doing this forward may be a clue on 
   how to do this in a fxnal style *)