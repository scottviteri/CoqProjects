Module Type Typ.
  Parameter Inline(10) T : Type.
End Typ.

Module Type HasBinOperation(Import M : Typ).
  Parameter f : T -> T -> T.
End HasBinOperation.

Module Type Magma <: Typ := Typ <+ HasBinOperation.

Module Type IsAssociative(Import M : Magma).
  Axiom assoc : forall (a b c : T), f (f a b) c = f a (f b c).
End IsAssociative.

Module Type Semigroup <: Magma := Magma <+ IsAssociative.

Module Type HasUnit(Import M : Magma).
  Parameter u : T.
  Axiom ru : forall a : T, (f a u) = a.
  Axiom lu : forall a : T, (f u a) = a.
End HasUnit.

Module Type UnitalMagma <: Magma := Magma <+ HasUnit.

Module Type Monoid <: Semigroup :=  Semigroup <+ HasUnit.

Module MonoidExample : Monoid.
  Definition T := nat.
  Definition f := plus.
  
  Lemma assoc : forall (a b c : T), f (f a b) c = f a (f b c).
    intros. unfold f. induction a as [| a' IHa].
    { reflexivity. }
    { simpl. apply f_equal, IHa. }
  Qed.
  
  Definition u := 0.

  Lemma ru : forall a : T, (f a u) = a.
  Proof. intros. unfold f. unfold u. rewrite <- plus_n_O. reflexivity. Qed.

  Lemma lu : forall a : T, (f u a) = a. 
  Proof. intros. unfold f, u. reflexivity. Qed.
End MonoidExample.

Module Type HasInverse(Import M : UnitalMagma).
  Parameter inv : T -> T.
  Axiom r_inv : forall a : T, f a (inv a) = u.
  Axiom l_inv : forall a : T, f (inv a) a = u.
End HasInverse.

Module Type IsCommutative(Import M : Magma).
  Axiom comm : forall a b : T, f a b = f b a.
End IsCommutative.

Module Type Group <: Monoid := Monoid <+ HasInverse.

Module Type AbelianGroup <: Group := Group <+ IsCommutative.

