Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d : day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end.

Compute (next_weekday friday).
Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday saturday) = sunday.
Proof.
  simpl. reflexivity. 
Qed.

Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b : bool) : bool :=
  match b with 
  | true => false
  | false => true
  end.

Compute (negb false).

Definition andb (b1 b2 : bool) : bool :=
  match b1 with 
  | true => b2  
  | false => false
  end.

Definition orb (b1 b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_bools : (orb false (andb true  true)) = true.
Proof.
  simpl. reflexivity.
Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_bools' : (false || (true && true)) = true.
Proof.
  simpl. reflexivity.
Qed.

Definition nandb (b1 b2 : bool) : bool :=
  match b1 with
  | true => (negb b2)
  | false => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1 b2 b3 : bool) : bool :=
  match b1 with
  | true => (andb b2 b3)
  | false => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check true.
Check (negb true).
Check negb.

Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.

Inductive color : Type :=
  | black : color
  | white : color
  | primary : rgb -> color.

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

Compute isred(primary red).

Module NatPlayground.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S m => m
  end.

End NatPlayground.

Check (S (S (S 0))).

Definition minustwo (n : nat) : nat :=
  match n with 
  | (S (S m)) => m
  | (S 0) => 0 
  | 0 => 0
  end.

Compute(minustwo 2).
Compute(minustwo 3).

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | 0 => true
  | 1 => false
  | (S (S m)) => (evenb m)
  end.

Compute (evenb 2).

Fixpoint oddb (n : nat) : bool :=
  (negb (evenb n)).

Compute (oddb 3).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.

Fixpoint plus (n m : nat) : nat :=
  match n with
  | 0 => m
  | (S n') => S (plus n' m)
  end.

Compute (plus 2 3).

Fixpoint multiply (n m : nat) : nat :=
  match n with
  | 0 => 0
  | (S n') => (plus m (multiply n' m))
  end.

Compute (multiply 2 4).

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m : nat) : nat :=
  match (n, m) with
  | (0,_) => 0
  | (S _, 0) => n
  | (S n',S m') => (minus n' m')
  end.

Compute (minus 4 3).

End NatPlayground2.

(*
Fixpoint exp1 (n m : nat) : nat :=
  match (n, m) with
  | (0,_) => 0
  | (S _, 0) => 1
  | (S _, S m') => (mult n (exp1 n m'))
  end.

Compute (exp1 2 3). 
*)

Fixpoint exp (base power : nat) : nat :=
  match power with 
  | 0 => 1
  | (S power') => (mult base (exp base power'))
  end.

Compute (exp 2 3).

(* Ex 1 *)
Fixpoint factorial (n : nat) : nat :=
  match n with
  | 0 => S 0
  | (S n') => (mult n (factorial n'))
  end.

Compute (factorial 3).

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                      (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                      (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Check ((0 + 1) + 1).

Fixpoint beq_nat (n m : nat) : bool :=
  match (n, m) with
  | (0,0) => true 
  | (S _, 0) => false
  | (0, S _) => false
  | (S n', S m') => (beq_nat n' m')
  end.

Compute (beq_nat 2 2).

(*
Fixpoint beq_nat2 (n m : nat) : bool :=
  match n with
  | 0 => match m with
         | 0 => true
         | (S _) => false
         end
  | (S n') => match m with
             | 0 => false
             | (S m') => (beq_nat2 n' m')
             end
  end.

Compute (beq_nat2 4 4).
*)


Fixpoint leb (n m : nat) : bool :=
  match n with
  | 0 => true
  | (S n') => match m with
              | 0 => false
              | (S m') => (leb n' m')
              end
  end.

Compute (leb 2 3).
Compute (leb 2 2).
Compute (leb 3 2).

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.


(* Ex 1 *)
Definition blt_nat (n m : nat) : bool := 
  (andb (leb n m) (negb (beq_nat n m))).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. split. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. split. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. split. Qed.

Theorem neutralzero : forall n : nat, (plus 0 n) = n.
Proof. intros. simpl. reflexivity. Qed.

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof. intros n. reflexivity. Qed.

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof. intros n. simpl. reflexivity. Qed.

Theorem mult_0_l : forall n : nat, (mult 0 n) = 0.
Proof. intros n. simpl. reflexivity. Qed.

Theorem plus_id_example : forall n m : nat,
  n = m -> (plus n n) = (plus m m).
Proof.
  intros n m H.
  rewrite <- H.
  reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
  intros n m o.
  intros H1 H2.
  rewrite <- H2.
  rewrite <- H1.
  reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros.
  rewrite -> neutralzero.
  reflexivity.
Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros.
  rewrite -> plus_1_l.
  rewrite <- H.
  reflexivity.
Qed.

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros.
  destruct n as [| n'].
  - rewrite -> neutralzero. simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros.
  destruct b.
  - simpl. reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative : forall b c, 
  andb b c = andb c b.
Proof.
  intros.
  destruct b.
  - simpl. destruct c. 
   + reflexivity.
   + reflexivity.
  - simpl. destruct c; reflexivity.
Qed.

Theorem andb_commutative' : forall b c, 
  andb b c = andb c b.
Proof.
  intros b c. destruct b.
  { destruct c; reflexivity. }
  { destruct c; reflexivity. }
Qed.

Theorem andb3_exchange :
 forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d.
  destruct b.
  { simpl. destruct c.
    - destruct d; reflexivity.
    - destruct d; reflexivity.
  } 
  { simpl. destruct c; reflexivity. }
Qed.

Theorem plus_1_neq_0' : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros [|n]; reflexivity.
Qed.

Theorem andb_commutative'' : forall b c, 
  andb b c = andb c b.
Proof.
  intros [] []; reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros [] [].
  - simpl. reflexivity.
  - simpl. intro. assumption.
  - simpl. intro. reflexivity.
  - simpl. intro. assumption.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof. intros [| n']; reflexivity. Qed.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Fixpoint plus' (n m : nat) : nat :=
  match n with
  | 0 => m
  | S n' => S (plus' n' m)
  end.

Theorem identity_fn_applied_twice : 
  forall (f : bool -> bool),
   (forall (x : bool), f x = x) ->
    forall (b : bool), f (f b) = b.
Proof. 
  intros f H b. rewrite H,H. reflexivity.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
   (andb b c = orb b c) -> b = c.
Proof.
  intros [] []; simpl; intro H.
  - reflexivity. 
  - inversion H.
  - inversion H.
  - reflexivity.
  Qed.

Inductive bin : Type :=
| zero : bin
| m2 : bin -> bin
| m2p1 : bin -> bin.

Fixpoint incr (n : bin) : bin :=
  match n with
  | zero => m2p1 zero
  | m2 n' => m2p1 n'
  | m2p1 n' => m2 (incr n')
  end.

Compute incr zero.
Compute incr (m2p1 zero).

Fixpoint bin_to_nat (n : bin) : nat :=
  match n with
  | zero => 0
  | m2 n' => 2 * (bin_to_nat n')
  | m2p1 n' => 2 * (bin_to_nat n') + 1
  end.

Compute bin_to_nat (m2 (m2p1 zero)).
