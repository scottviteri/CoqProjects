(*
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Import ListNotations.
*)
Require Export Basics.
(* Require Import Arith. *)
(* Require Import Ascii. *)

Inductive string : Set :=
  | EmptyString : string
  | String : ascii -> string -> string.

Delimit Scope string_scope with string.
Local Open Scope string_scope.

(*
Theorem string_dec : forall (s1 s2 : string), (s1 = s2) /\ (s1 <> s2).
*)

Reserved Notation "x ++ y" (right associativity, at level 60).

Fixpoint append (s1 s2 : string) : string :=
  match s1 with
  | EmptyString => s2
  | String c s1' => String c (s1' ++ s2)
  end
where "s1 ++ s2" := (append s1 s2) : string_scope.

Search plus.

Fixpoint length (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => S (length s')
  end.

Inductive option (A : Type) : Type :=
  | Some : A -> option A
  | None : option A.

Fixpoint get (n : nat) (s : string) {struct s} : option ascii :=
  match s with 
  | EmptyString => None ascii
  | String c s' => if (beq_nat n 0) 
                     then (Some ascii c) 
                     else (get (pred n) s')
  end.

