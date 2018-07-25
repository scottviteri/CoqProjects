Set Warnings "-notation-overridden,-parsing".
Require Export Poly.

Theorem silly1 : forall (n m o p : nat),
  n = m -> [n;o] = [n;p] -> [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1. apply eq2.
Qed.

Theorem silly2 : forall (n m o p : nat),
     n = m ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p Eq_nm H.
  rewrite Eq_nm. apply H. reflexivity.
Qed.

Theorem silly_ex : (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  intros H1 H2. inversion H2.
Qed.

Theorem silly3 : forall (n : nat),
     true = beq_nat n 5 ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H. symmetry. simpl. apply H.
Qed.
  
Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' -> l' = rev l.
Proof.
  intros l l' H. rewrite H. symmetry. apply rev_involutive.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
  [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1, eq2. reflexivity.
Qed.

Theorem trans_eq : forall (X : Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1, eq2. reflexivity.
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
  [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]). 
  - apply eq1.
  - apply eq2.
Qed.

Example trans_eq_exercise : forall (n m o p : nat),
  m = (minustwo o) -> (n + p) = m -> (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  apply trans_eq with m; assumption.
Qed.

Theorem S_injective : forall (n m : nat), 
  S n = S m -> n = m.
Proof. intros n m H. inversion H. reflexivity. Qed.

Theorem inversion_ex1 : forall (n m o : nat), 
  [n;m] = [o;o] -> [n] = [m].
Proof. intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n m : nat),
  [n] = [m] -> n = m.
Proof. intros n m H. inversion H as [Hnm]. reflexivity. Qed.

Example inversion_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof. 
  intros X x y z l j eq1 eq2. 
  inversion eq1 as [H1]. inversion eq2 as [H2]. 
  symmetry. assumption.
Qed.

Theorem beq_nat_0_l : 
  forall n, beq_nat 0 n = true -> n = 0.
Proof.
  intros n H. destruct n as [| n'].
  - reflexivity.
  - inversion H.
Qed.

Theorem inversion_ex4 : forall (n : nat),
 S n = 0 -> 2 + 2 = 5.
Proof.
  intros n H. inversion H.
Qed.

Theorem inversion_ex5 : forall (n m : nat),
  false = true -> [n] = [m].
Proof. intros n m H. inversion H. Qed.

Example inversion_ex6 : forall (X : Type)
  (x y z : X) (l j : list X),
  x :: y :: l = [] ->
  y :: l = z :: j -> x = z.
Proof. intros X x y z l j H. inversion H. Qed.

Theorem f_equal : forall (A B : Type) (f : A -> B) (x y : A),
 x = y -> f x = f y.
Proof. intros A B f x y eq1. rewrite eq1. reflexivity. Qed.

Theorem S_equal_rev : forall (n m : nat),
  S n = S m -> n = m.
Proof. intros n m H. inversion H. reflexivity. Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
  beq_nat (S n) (S m) = b -> beq_nat n m = b.
Proof. intros n m b H. simpl in H. apply H. Qed.

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
  true = beq_nat n 5 ->
  true = beq_nat (S (S n)) 7.
Proof.
  intros n H1 H2. symmetry in H2. 
  apply H1 in H2. symmetry in H2. 
  apply H2.
Qed.

Theorem plus_n_n_injective : forall n m, 
  n + n = m + m -> n = m.
Proof.

  intros n. induction n as [| n'].
  { intros m H. simpl in H. destruct m. 
    { reflexivity. }
    { simpl in H. inversion H. }
  }
  {
    intros m H. simpl in H. rewrite <- plus_n_Sm in H. 
    assert (forall p : nat, S p = m -> n' + n' = p + p).
      { intros P PH. rewrite <- PH in H. simpl in H. rewrite <- plus_n_Sm in H.
        inversion H as [H1]. reflexivity.
      }
    destruct m. { symmetry in H. simpl in H. inversion H. }
    simpl in H. rewrite <- plus_n_Sm in H. 
    apply S_equal_rev in H. apply S_equal_rev in H.
    apply IHn' in H. apply f_equal. apply H.
  }
Qed.

Theorem double_injective : forall n m,
  double n = double m -> n = m.
Proof.
  intros n. induction n as [| n']. 
  { simpl. intros m eq. destruct m as [| m'].
    { reflexivity. } { inversion eq. }
  }
  { intros m eq. simpl in eq. destruct m as [| m'].
    { inversion eq. } 
    { apply f_equal. apply IHn'.
      inversion eq. reflexivity.
    }
  }
Qed.

Theorem beq_nat_true : forall n m,
  beq_nat n m = true -> n = m.
Proof.
  intros n. induction n as [| n'].
  { intros m H. destruct m as [| m'].
    { reflexivity. } { inversion H. }
  }
  { intros m H. destruct m as [| m'].
    { inversion H. } 
    { apply f_equal, IHn'. 
      simpl in H. apply H.
    }
  }
Qed.

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. generalize dependent n.
  induction m as [| m'].
  { intros n H. destruct n as [| n']. 
    { reflexivity. } { inversion H. }
  }
  { intros n eq. destruct n as [| n'].
    { simpl in eq. inversion eq. }
    { apply f_equal, IHm'. inversion eq. reflexivity. }
  }
Qed.

Theorem beq_id_true : forall x y, 
  beq_id x y = true -> x = y.
Proof.
  intros [m] [n]. simpl. intros H. 
  assert (G : (m = n)). { apply beq_nat_true, H. }
  rewrite G. reflexivity.
Qed.

Theorem nth_error_after_last : forall (n : nat) (X : Type) (l : list X),
  length l = n -> nth_error l n = None.
Proof.
  intros n X l len. 
  generalize dependent n.
  generalize dependent X. 
  induction l as [| x l' IHl'].
    { reflexivity. } 
    { intros n H. destruct n as [| n'].
      { inversion H. }
      { simpl. apply IHl'. 
        inversion H. reflexivity.
      }
    }
Qed.

Definition square n := n * n.
 
(*
Lemma mult_distrib : forall (n m o : nat), n * (m + o) = n * m + n * o.
Proof.
  intros n m o. induction n as [| n' IHn'].
  { reflexivity. } 
  { simpl. rewrite -> plus_assoc, plus_assoc.
    apply f_equal with (f:=fun k => m + k). 
    rewrite -> plus_comm. rewrite <- plus_assoc. rewrite <- plus_comm.
    rewrite -> plus_assoc. rewrite < plus_comm. 


Lemma mult_assoc : forall (n m o : nat), (n * m) * o = n * (m * o).
Proof.
  intros n m o. induction n as [| n' IHn'].
  { reflexivity. } { simpl. rewrite <- IHn'. 

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m. unfold square.
*)

