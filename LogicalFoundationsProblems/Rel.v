Set Warnings "-notation-overidden,-parsing".

Definition relation (X : Type) := X -> X -> Prop.

Print le.

Check le : nat -> nat -> Prop.
Check le : relation nat.

Definition partial_function {X : Type} (R : relation X) := 
 forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Theorem ex_falso_quodlibet : forall (P : Prop), False -> P.
Proof. intros. destruct H. Qed.

Definition reflexive {X : Type} (R : relation X) :=
 forall a : X, R a a.

Definition transitive {X : Type} (R : relation X) :=
 forall a b c : X, R a b -> R b c -> R a c.

Definition symmetric {X : Type} (R : relation X) :=
 forall a b : X, R a b -> R b a -> R a b.

Definition equivalence {X : Type} (R : relation X) :=
 (reflexive R) /\ (symmetric R) /\ (transitive R).

