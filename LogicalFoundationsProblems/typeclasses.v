(* Typeclasses *) 
Require Import String. 
Require Import Ascii.
Require Import Nat.
Require Import List.

Locate Nat.
Locate Equivalence.
Class Show A : Type :=
  {
    show : A -> string
  }.

Locate string.
Check String "a" EmptyString.
Compute "Hello world!" %string.
Compute (append "a" "b")%string.

Instance showBool : Show bool :=
  {
    show := fun b : bool => 
            if b then "true"%string else "false"%string
  }.

Check true.
Compute show true.

Inductive color := Red | Green | Blue.
Instance showColor : Show color :=
  {
    show := 
      fun c : color => 
        match c with
        | Red => "Red"%string
        | Green => "Green"%string
        | Blue => "Blue"%string
      end
  }.

Compute (show Green).

Check show.

Fixpoint leb (n m : nat) : bool :=
  match n with 
  | 0 => true
  | S n' => match m with
            | 0 => false
            | S m' => leb n' m'
            end
  end.

Compute leb 2 3.
Compute leb 3 2.
Compute 4 - 3.

Compute modulo 2 3. 

Fixpoint string_of_nat_aux (time n : nat) (acc : string) : string :=
    let d := match (modulo n 10) with
             | 0 => "0"%string | 1 => "1"%string | 2 => "2"%string 
             | 3 => "3"%string | 4 => "4"%string | 5 => "5"%string
             | 6 => "6"%string | 7 => "7"%string | 8 => "8"%string
             | _ => "9"%string
             end in
    let acc' := (append d acc) in
    match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
      | 0 => acc'
      | n' => string_of_nat_aux time' n' acc'
      end
    end.

Definition string_of_nat (n : nat) : string :=
  string_of_nat_aux n n "".

Instance showNat : Show nat :=
  {
    show := string_of_nat
  }.

Compute (show 42).
Check pair 2 true.
Compute fst (pair 2 true).

Instance showNatBool : Show (nat * bool) :=
  {
    show := fun p => (append (show (fst p)) (show (snd p)))
  }.

Compute show (pair 2 true).

Definition showOne {A : Type} `{Show A} (a : A) : string :=
  (append "The value is " (show a)).

Compute showOne (pair 2 true).

Definition showTwo {A B : Type} 
  `{Show A} `{Show B} (a : A) (b : B) : string :=
  "First is " ++ (show a) ++ " and second is " ++ show b.

Compute (showTwo true 42).

Class Eq A :=
  {
    eqb: A -> A -> bool;
  }.

Print negb.
Compute (negb true).
Instance eqBool : Eq bool :=
  {
    eqb := fun (b c : bool) => 
      if b then c else (negb c)
  }.

Fixpoint beq_nat (n m : nat) : bool :=
  match (n,m) with
  | (0,0) => true
  | (S n', 0) => false
  | (0,S m') => false
  | (S n', S m') => beq_nat n' m'
  end.

Compute beq_nat 2 2.
Compute beq_nat 2 1.

Instance eqNat : Eq nat :=
  {
    eqb := beq_nat
  }.

Instance eqBoolBool : Eq (bool -> bool) :=
  {
    eqb := fun (f g : bool -> bool) =>
      let gtrue := (g true) in 
      let gfalse := (g false) in
      match (f true) with
      | gtrue => match (f false) with
                  | gfalse => true
                  end
      end
  }.

Definition f : bool -> bool :=
  fun b : bool => match b with
                  | true => true
                  | false => false
                  end.
Compute (f true).
Compute (eqb f f).

Check show.
Compute (append "1" "2").

Open Scope string_scope.
Instance showPair {A B : Type} `{Show A} `{Show B} : Show (A * B) :=
  {
    show p := 
      let (a,b) := p in 
        "(" ++ show a ++ "," ++ show b ++ ")"
  }.
Close Scope string_scope.

Compute (show (true,42)).

Instance eqPair {A B : Type} `{Eq A} `{Eq B} : Eq (A*B) :=
  {
    eqb p1 p2 :=
      let (p1a,p1b) := p1 in
      let (p2a,p2b) := p2 in
      andb (eqb p1a p2a) (eqb p1b p2b)
  }.

Fixpoint showListAux {A : Type} (s : A -> string) (l : list A) : string :=
  match l with
  | nil => ""
  | h :: nil  => s h
  | h :: t => s h ++ showListAux s t
  end.

Instance showList {A : Type} `{Show A} : Show (list A) :=
  {
    show l := showListAux show l
  }.

Compute show (cons 1 (cons 2 nil)).

Instance showOption {A : Type}  `{Show A} : Show (option A) :=
  {
    show opt := 
      match opt with
      | None => ""%string
      | Some a => show a
      end
  }.

Print option.
Compute show (Some 5).

Instance eqOption {A : Type} `{Eq A} : Eq (option A) :=
  {
    eqb opt1 opt2 :=
      match (opt1,opt2) with
      | (None,None) => true
      | (Some a,None) => false
      | (None,Some a) => false
      | (Some a1,Some a2) => eqb a1 a2
      end
  }.

Fixpoint eqListAux {A : Type} (eqA : A -> A -> bool) (l1 l2 : list A) :=
  match (l1,l2) with
  | (nil,nil) => true
  | (cons h t,nil)=> false
  | (nil,cons h t)=> false
  | (cons h1 t1, cons h2 t2)=> andb (eqA h1 h2) (eqListAux eqA t1 t2)
  end.

Instance eqList {A : Type} `{Eq A} : Eq (list A) :=
  {
    eqb := eqListAux eqb
  }.

Compute eqb (Some 3) (Some 4).
Compute eqb (Some 4) (Some 4).

Instance boolToA {A : Type} `{Eq A} : Eq (bool -> A) :=
  {
    eqb bToA1 bToA2 := 
      (andb
        (eqb (bToA1 true) (bToA2 true))
        (eqb (bToA1 false) (bToA2 false)))
  }.

Definition f1 : bool -> bool -> nat :=
  fun b1 => 
    match b1 with
    | true => (fun b2 => 3)
    | false => (fun b2 => 4)
    end.

Compute eqb f1 f1.

Class Ord A `{Eq A} : Type :=
  {
    le : A -> A -> bool
  }.
Check Ord.
Check nat.
Print Nat.leb.
Print Nat.
Instance natOrd : Ord nat :=
  {
    le := Nat.leb
  }.

Definition max {A : Type} `{Ord A} (x y : A) : A :=
  if (le x y) then y else x.

Instance optOrd {A : Type} `{Ord A} : Ord (option A) :=
  {
    le opt1 opt2:= 
      match (opt1,opt2) with
      | (None,None)=>true
      | (Some a,None)=>false
      | (None, Some a)=>true
      | (Some a1, Some a2)=> le a1 a2
      end
  }.

Print fst.
Instance pairOrd {A B : Type} `{Ord A} `{Ord B} : Ord (A*B) :=
  {
    le p1 p2 := andb (le (fst p1) (fst p2)) (le (snd p1) (snd p2)) 
  }.

Compute le (1,Some 1) (2,Some 2).
Compute le (1,Some 4) (2, Some 2).

Fixpoint listOrdAux {A : Type} (eqA : A -> A -> bool) (l1 l2 : list A) :=
  match (l1,l2) with
  | (nil,nil) => true
  | (cons h t,nil) => false
  | (nil, cons h t) => false
  | (cons h1 t1, cons h2 t2) => (andb (eqA h1 h2) (listOrdAux eqA t1 t2))
  end.
  
Instance listOrd {A : Type} `{Ord A} : Ord (list A) :=
  {
    le := listOrdAux le 
  }.


Compute le (cons 1 nil) (cons 2 nil).
Compute le (cons 2 nil) (cons 1 nil).
Compute le (cons 1 nil) (nil).

Generalizable Variables A.
Definition showOne1 `{Show A} (a : A) : string :=
  "The value is " ++ show a.

Print showOne1.

Definition showOne2 `{_ : Show A} (a : A) : string :=
  "The value is " ++ show a.

Definition showOne3 `{H : Show A} (a : A) : string :=
  "The value is " ++ show a.

Definition showOne4 `{Show} a : string :=
  "The value is " ++ show a.

Set Printing Implicit.
Print showOne.
Print showOne1.
Unset Printing Implicit.

Definition max1 `{Ord A} (x y : A) :=
  if le x y then y else x.

Set Printing Implicit.
Print max1.
Check Ord.
Unset Printing Implicit.

Generalizable Variables x y.
Lemma commutativity_property : `{x + y = y + x}.
Proof. intros x y. induction x as [| n' IH].
  { simpl. apply plus_n_O. }
  { simpl. rewrite <- plus_n_Sm. f_equal. apply IH. }
Qed.
Definition implicit_fun := `{x + y}.
Print implicit_fun.

Compute (@implicit_fun 2 3).

Definition implicit_fun1 := `(x + y).
Print implicit_fun1.
Compute (implicit_fun1 2 3).

Record Point :=
  Build_Point 
    {
      px : nat;
      py : nat
    }.

(* 
Inductive Point :=
  | Build_Point : nat -> nat -> Point.
*)
Check (Build_Point 2 4).

Check {| px:=2; py:=4 |}.
Check {| py:=4; px:=2 |}.

Definition r : Point := {| px:=2; py:=4 |}.
Compute r.(px).

Record LabeledPoint (A : Type) :=
  Build_LabeledPoint
    {
      lx : nat;
      ly : nat;
      label : A
    }.

Check {| lx:=2; ly:=4; label:="hello"%string |}.

Set Printing All.
Print Show.
Unset Printing All.

Print showNat.

Set Printing All.
Print show.
Unset Printing All.

Definition eg42 := show 42.
Set Printing Implicit.
Print eg42.
Unset Printing Implicit.

Print HintDb typeclass_instances.

Set Typeclasses Debug.
Check (show 42).
Check (show (true,42)).
Unset Typeclasses Debug.

(* Typeclasses and Proofs *)

Class EqDec (A : Type) {H : Eq A} :=
  {
    eqb_eq : forall x y, 
            eqb x y = true <-> x = y
  }.

Instance eqdecNat : EqDec nat :=
  {  
    eqb_eq := PeanoNat.Nat.eqb_eq
  }.

Instance eqdecBool' : EqDec bool :=
  {}.
Proof.
  intros x y. destruct x; destruct y;
  simpl; unfold iff; auto.
Qed.

Instance eqdecBool'' : EqDec bool.
Proof.
  constructor.
  intros x y. destruct x; destruct y;
  simpl; unfold iff; auto.
Qed.

Lemma eqb_fact `{EqDec A} : 
  forall (x y z : A), eqb x y = true
  -> eqb y z = true -> x = z.
Proof.
  intros x y z Exy Eyz.
  rewrite eqb_eq in Exy.
  rewrite eqb_eq in Eyz.
  subst. reflexivity.
Qed.

(* substructures *)
Require Import Coq.Relations.Relation_Definitions.

Class Reflexive (A : Type) (R : relation A) :=
  {
    reflexivity : forall x, R x x
  }.

Class Transitive (A : Type) (R : relation A) :=
  {
    transitivity : forall x y z, R x y -> R y z -> R x z
  }.

Class Symmetric (A : Type) (R : relation A) :=
  {
    symmetry : forall x y, R x y -> R y x
  }.

Generalizable Variables z w R.

Lemma trans3 : forall `{Transitive A R},
  `{R x y -> R y z -> R z w -> R x w}.
Proof.
  intros. apply (transitivity x z w).
  - apply (transitivity x y z); assumption. 
  - assumption.
Qed.

Class PreOrder (A : Type) (R : relation A) :=
  { PreOrder_Reflexive :> Reflexive A R;
    PreOrder_Transitive :> Transitive A R }.

Class Poset (A : Type) (R : relation A)  `{PreOrder A R} :=
  {
    Poset_Symmetric :> Symmetric A R
  }.


Lemma trans3_pre : forall `{PreOrder A R},
  `{R x y -> R y z -> R z w -> R x w}.
Proof. 
  intros. eapply trans3; eassumption.
Qed.

From mathcomp.ssreflect Require Import ssreflect ssrbool.
 
Print decidable.

Class Dec (P : Prop) : Type :=
  {
    dec : decidable P
  }.

Instance EqDec__Dec {A} `{H : EqDec A} (x y : A) : Dec (x = y).
Proof. constructor. unfold decidable.
  destruct (eqb x y) eqn:E.
  - left. rewrite <- eqb_eq. assumption.
  - right. intros C. rewrite <- eqb_eq in C. rewrite E in C. inversion C.
Qed.

Instance Dec_conj {P Q} {H : Dec P} {I : Dec Q} : Dec (P /\ Q).
Proof.
  constructor. unfold decidable.
  destruct H as [D]; destruct D; destruct I as [D]; destruct D;
  auto; right; intro; destruct H; contradiction.
Qed.