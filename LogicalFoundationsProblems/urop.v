Set Warnings "-notation-overriden,-parsing".

(* CIC built from function types and inductive types *)

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4: forall n, ev n -> ev (4 + n).
Proof. intros. simpl. apply ev_SS. apply ev_SS. apply H. Qed.

Inductive le : nat -> nat -> Prop :=
| le_n : forall n, le n n
| le_S : forall n m, (le n m) -> (le n (S m)).

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Definition isZero (n : nat) : bool :=
  match n with
    | O => true
    | S _ => false
  end.

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

Inductive nat_list : Set :=
| NNil : nat_list
| NCons : nat -> nat_list -> nat_list.


Fixpoint nlength (ls : nat_list) : nat :=
  match ls with
    | NNil => O
    | NCons _ ls' => S (nlength ls')
  end.

Fixpoint napp (ls1 ls2 : nat_list) : nat_list :=
  match ls1 with
    | NNil => ls2
    | NCons n ls1' => NCons n (napp ls1' ls2)
  end.

Inductive list (T : Set) : Set :=
| Nil : list T
| Cons : T -> list T -> list T.

Inductive bool : Set :=
| true
| false.

Definition negb (b : bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Definition negb' : bool -> bool
  := fun (b : bool) => match b with
                       | true => false
                       | false => true
                       end.


Fixpoint plus (n m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.


Inductive Time :=
| zero_t : Time
| S_t : Time -> Time.

Inductive Loc :=
| zero_l : Loc
| S_l : Loc -> Loc.

Inductive Person : Set :=
| Mary : Person
| Joe  : Person.

Inductive At : Person -> Time -> Loc -> Prop :=
| At1: Mary -> zero_t -> zero_l -> True.
