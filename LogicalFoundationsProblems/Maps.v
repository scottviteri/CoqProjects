Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Export Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Import ListNotations.

Definition beq_string x y :=
  if string_dec x y then true else false.

Theorem beq_string_refl : forall s, true = beq_string s s.
Proof.
  intros s. unfold beq_string. destruct (string_dec s s) as [|Hs].
  { reflexivity. }
  { destruct Hs. reflexivity. }
Qed.

Theorem beq_string_true_iff : 
  forall (x y : string), beq_string x y = true <-> x = y.
Proof.
  intros x y. unfold beq_string. 
  destruct (string_dec x y) as [|Hs]. 
  { subst. split; reflexivity. }
  { split. { intros H. inversion H. }
           { intros H. subst. destruct Hs. reflexivity. }
}
Qed. 

Theorem beq_string_false_iff : forall x y : string,
  beq_string x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- beq_string_true_iff.
  rewrite not_true_iff_false. reflexivity.
Qed.

Theorem false_beq_string : 
  forall x y : string, x <> y -> beq_string x y = false.
Proof.
  intros x y. rewrite beq_string_false_iff. intros H. apply H.
Qed.

Definition total_map (A : Type) := string -> A.

Definition t_empty {A: Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} 
  (m : total_map A) (x : string) (v : A) :=
fun x' => if beq_string x x' then v else m x'.

Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true) "bar" true.

Notation "{ --> d }" := (t_empty d) (at level 0).

Notation "m '&' { a --> x }" :=
  (t_update m a x) (at level 20).
Notation "m '&' { a --> x ; b --> y }" :=
  (t_update (m & { a --> x }) b y) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z }" :=
  (t_update (m & { a --> x ; b --> y }) c z) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t }" :=
    (t_update (m & { a --> x ; b --> y ; c --> z }) d t) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t ; e --> u }" :=
    (t_update (m & { a --> x ; b --> y ; c --> z ; d --> t }) e u) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v }" :=
    (t_update (m & { a --> x ; b --> y ; c --> z ; d --> t ; e --> u }) f v) (at level 20).

Definition examplemap' :=
  { --> false } & { "foo" --> true ; "bar" --> true }.

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
  { --> v } x = v.
Proof.
  intros A x v. unfold t_empty. reflexivity.
Qed.

Lemma t_update_eq : forall A (m : total_map A) x v,
  (m & {x --> v}) x = v.
Proof.
  intros A m x v. unfold t_update. 
  rewrite <- beq_string_refl. reflexivity.
Qed.

Theorem t_update_neq : forall (X : Type) v x1 x2 (m : total_map X),
 x1 <> x2 -> (m & {x1 --> v}) x2 = m x2.
Proof.
  intros X v x1 x2 m H. unfold t_update.
  rewrite false_beq_string.
  - reflexivity.
  - apply H.
Qed.

Theorem nested_ifs : 
  forall (P: bool) (A : Type) (X Y Z : A), 
    (if P then X else (if P then Y else Z)) =
    (if P then X else Z).
Proof.
  intros P X Y Z. destruct P; reflexivity.
Qed.

Theorem t_update_shadow : forall A (m : total_map A) v1 v2 x,
  m & {x --> v1 ; x --> v2} = m & {x --> v2}.
Proof.
  intros A m v1 v2 x. unfold t_update.
  extensionality i. destruct (beq_string x i); reflexivity.
Qed.

Lemma beq_stringP : forall x y, reflect (x = y) (beq_string x y).
Proof.
