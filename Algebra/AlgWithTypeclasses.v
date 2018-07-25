Require Import Coq.Relations.Relation_Definitions.
From mathcomp.ssreflect Require Import ssreflect ssrbool.
Require Import String. 
Require Import Ascii.
Require Import Nat.
Require Import List.


Locate Nat.

Class Eq A :=
  {
    eqb: A -> A -> bool;
  }.

Compute Nat.eqb 2 2.
Compute Nat.eqb 2 1.

Instance eqNat : Eq nat :=
  {
    eqb := Nat.eqb
  }.
Locate Nat.
Class EqDec (A : Type) {H : Eq A} :=
  {
    eqb_eq : forall x y, 
      eqb x y = true <-> x = y
  }.

Instance eqDecNat : EqDec nat :=
  {
    eqb_eq := PeanoNat.Nat.eqb_eq
  }.

Class Dec (P : Prop) : Type :=
  {
    dec : decidable P
  }.

Generalizable Variables A.

Class Magma A `{EqDec A} :=
  {
    binOp : A -> A -> A
  }.

Instance nat_magma : Magma nat :=
  {
    binOp := plus;
  }. 

Class Associative (A : Type) `{M : Magma A} :=
  {
    associativity : 
      forall x y z, 
        binOp (binOp x y) z = binOp x (binOp y z)
  }.

Class Semigroup A `{M : Magma A} :=
  {
    Sg_assoc :> Associative A
  }.

Theorem plus_assoc :
  forall a b c : nat, plus (plus a b) c = plus a (plus b c).
Proof.
  intros a b c. induction a as [| n IH].
  { reflexivity. }
  { simpl. f_equal. apply IH. }
Qed.

Instance nat_assoc : Associative nat :=
  {
    associativity := plus_assoc
  }.

Instance nat_semigroup : Semigroup nat :=
  { 
    Sg_assoc := nat_assoc
  }.


Class HasUnit (A : Type) `{Magma A} :=
  {
    unit_existence : 
      forall x, exists u, 
          andb (eqb (binOp x u) x) 
               (eqb (binOp u x) x)
  }.

Class UnitalMagma A `{M : Magma A} :=
  {
    UM_unit :> HasUnit A
  }.

Class Monoid A `{S : Semigroup A} :=
  {
    Mon_unit :> HasUnit A
  }.

Print eqb_eq.

Instance nat_monoid : Monoid nat.
Proof. constructor. constructor.
  intros x. exists 0. simpl.
  rewrite <- plus_n_O. unfold andb. 
  induction x as [| n' IH]. 
  { reflexivity. }
  { simpl. apply IH. }
Qed.

Class HasInverse (A : Type) `{M : UnitalMagma A} :=
  {
    inverse_existence : 
      forall x, exists xinv u, 
        andb 
          (andb (eqb (binOp x xinv) u) 
                (eqb (binOp xinv x) u))
          (andb (eqb (binOp x u) x) 
                (eqb (binOp u x) x))
  }.

(*
Class Group A `{Mon : Monoid A} :=
  {
    Gp_inv :> HasInverse A
  }.

Class Commutative (A : Type) `{M : Magma A} :=
  {
    commutativity : 
      forall x y, 
        (binOp x y) = (binOp y x)
  }.

Class AbelianGroup A `{G : Group A} :=
  {
    Ab_Gp_comm :> Commutative A
  }.
*)

