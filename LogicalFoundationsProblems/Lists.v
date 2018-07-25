Require Export Induction.
Module NatList.

Inductive natprod : Type :=
  | pair : nat -> nat -> natprod.

Check (pair 3 5).

Definition fst (p : natprod) : nat :=
  match p with
  | pair n _ => n
  end.

Definition snd (p : natprod) :=
  match p with 
  | pair _ m => m
  end.

Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with 
  | (x,_) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with 
  | (_,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (a,b) => (b,a)
  end.


Theorem surjective_pairing' : 
  forall (n m : nat), 
    (n,m) = (fst (n,m), snd (n,m)).
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem surjective_pairing : 
  forall (p : natprod), p = (fst p, snd p).
Proof.
  intros.
  destruct p as [n m]. simpl. reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros. destruct p as [m n]. simpl. reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros. destruct p as [m n]. simpl. reflexivity.
Qed.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | 0 => nil
  | S count' => (cons n (repeat n count'))
  end.

Compute (repeat 3 4).

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => 0
  | (cons n l') => 1 + (length l')
  end.

Compute (length (cons 1 (cons 2 nil))).
Compute (length [1;2;3]).

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | cons n l1' => cons n (app l1' l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Compute (length (app [1;2;3] [4;5;6])).
Compute (length ([1;2;3]++[4;5;6])).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default : nat) (l : natlist) : nat :=
  match l with 
  | nil => default
  | cons n l' => n
  end.

Compute (hd 2 [1;2;3]).
Compute (hd 2 nil).

Definition tl (l: natlist) : natlist :=
  match l with
  | nil => nil
  | cons h t => t
  end.

Definition tl' (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1 : hd 0 [1;2;3] = 1.
Proof. simpl. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l : natlist) : natlist :=
  match l with
  | nil => nil
  | 0 :: t => nonzeros t
  | h :: t => (cons h (nonzeros t))
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.

Fixpoint oddmembers (l : natlist) : natlist :=
  match l with 
  | nil => nil
  | h :: t => match (oddb h) with
              | true => h :: (oddmembers t)
              | false => (oddmembers t)
              end
  end.

Compute (oddmembers [1;5;2;2;3;3;2]).
Example test_oddmembers : (eq (oddmembers [1;5;4;3]) [1;5;3]).
Proof. simpl. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1,l2 with
  | nil,nil => nil
  | l1, nil => l1
  | nil, l2 => l2
  | h1::t1,h2::t2 => h1 :: h2 :: (alternate t1 t2)
  end.

(* 
Fixpoint alternate' (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (alternate' l2 t)
  end.
*)

Fixpoint alternate'' (l1 l2 : natlist) : natlist :=
  match l1 with
  | [] => l2
  | h1 :: t1 => match l2 with 
                | [] => l1
                | h2 :: t2 => h1 :: h2 :: (alternate'' t1 t2)
                end
  end.

Compute (alternate [1;2;3] [4;5;6]).
Compute (alternate'' [1;2;3] [4;5;6]).

Fixpoint In (n : nat) (l : natlist) : bool :=
  match l with
  | [] => false
  | h :: t => if (beq_nat n h) then true else (In n t)
  end.

Definition bag := natlist.

Fixpoint nat_beq (n m : nat) : bool :=
  match (n,m) with
  | (0,0) => true
  | (S _,0) => false
  | (0, S _) => false
  | (S n',S m') => nat_beq n' m'
  end.

Fixpoint count' (v : nat) (s : bag) : nat :=
  match s with
  | [] => 0
  | h :: t => match (nat_beq v h) with
              | false => count' v t
              | true => (S (count' v t))
              end
  end.

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | nil => 0
  | h :: t => if (nat_beq h v) then (S (count v t)) else (count v t)
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.

Definition sum : bag -> bag -> bag :=
 app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag :=
 cons v s.

Definition add' : nat -> bag -> bag :=
 cons.

Example test_add1 : count 1 (add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.
Example test_add2 : count 5 (add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Definition member (v : nat) (s : bag) : bool :=
  In v s.

Definition member' : nat -> bag -> bool := In.

Example test_member1: member 1 [1;4;1] = true.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
  | [] => []
  | h :: t => if (nat_beq v h) then t else h :: (remove_one v t)
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | [] => []
  | h :: t => if (nat_beq v h) then (remove_all v t) else h :: (remove_all v t)
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint subset (s1 : bag) (s2 : bag) : bool :=
  match s1 with 
  | [] => true
  | h1 :: t1 => 
    if (member h1 s2) then (subset t1 (remove_one h1 s2)) else false
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Theorem nil_app :  forall l : natlist, [] ++ l = l.
Proof. simpl. reflexivity. Qed.

Theorem tl_length_pred : forall l : natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l']; reflexivity. 
Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IH1'].
  - simpl. reflexivity.
  - simpl. rewrite -> IH1'. reflexivity.
Qed.

Fixpoint rev (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

(* length (rev l' ++ [n]) = S (length (rev l')) *)
Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
 length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl']. 
  - reflexivity.
  - simpl. rewrite -> app_length.
    rewrite -> plus_comm. simpl.
    rewrite <- IHl'. reflexivity.
Qed.

Theorem cons_to_append : forall (n : nat) (l : natlist),
  n :: l = [n] ++ l.
Proof.
  intros n l. destruct l as [| n' l']; reflexivity.
Qed.

Theorem app_nil_r : forall l : natlist, 
  l ++ [] = l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite -> IHl'. reflexivity.
Qed. 

Theorem rev_app_distr : forall l1 l2 : natlist, 
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl1', app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist, rev (rev l) = l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite -> rev_app_distr, IHl'. reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4. rewrite -> app_assoc, app_assoc. reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist, 
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - reflexivity.
  - simpl. rewrite -> IHl1'. destruct n.
    + reflexivity.
    + reflexivity.
Qed.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1 with 
  | [] => match l2 with 
          | [] => true
          | h::t => false
          end
  | h1::t1 => match l2 with
            | [] => false
            | h2::t2 => 
              if (beq_nat h1 h2) 
                then (beq_natlist t1 t2)
                else false
            end
  end.

Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
Proof. reflexivity. Qed.

Example test_beq_natlist2 :
  beq_natlist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.

Example test_beq_natlist3 :
  beq_natlist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem beq_nat_refl : forall n : nat, true = beq_nat n n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. destruct n.
    + simpl. rewrite <- IHl'. reflexivity.
    + simpl. rewrite <- beq_nat_refl, IHl'. reflexivity.
Qed.

Theorem count_member_nonzero : forall (s : bag), 
  leb 1 (count 1 (1 :: s)) = true.
Proof.
  intros s. reflexivity.
Qed.

Fixpoint leb (n m : nat) : bool :=
  match n with 
  | 0 => true
  | S n' => match m with
            | 0 => false
            | S m' => leb n' m'
            end
  end.

Theorem ble_n_Sn : forall n, leb n (S n) = true.
Proof.
  intros n. induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem remove_decreases_count : forall (s : bag),
  leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros s. induction s as [| n s' IHs'].
  - reflexivity.
  - simpl. destruct n.
   + simpl. rewrite -> ble_n_Sn. reflexivity.
   + simpl. rewrite -> IHs'. reflexivity.
Qed.

Theorem rev_pres_empty : forall l, [ ] = rev l <-> [ ] = l.
Proof.
  split. 
  {
    intros H. destruct l.
    + reflexivity.
    + assert (rev [] = n :: l) as G.
    { rewrite -> H. rewrite -> rev_involutive. reflexivity. }
    rewrite <- G. simpl. reflexivity.
  }
  {
    intros H. destruct l. {reflexivity. } 
    {rewrite <- H. reflexivity. }
  }
Qed.

Theorem rev_flip : forall (n : nat) (l : natlist), rev ([n] ++ l) = rev l ++ [n].
Proof.
  intros n l. destruct l as [| n' l']; reflexivity.
Qed.

Theorem rev_one_element : forall n : nat, rev [n] = [n].
Proof.
  intros n. reflexivity.
Qed.

Theorem rev_injective : forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2. 
  induction l1 as [| n l1' IHl1']. 
  { 
    simpl. intros H. 
    assert (rev [] = l2) as G. { 
      rewrite -> H. rewrite -> rev_involutive. reflexivity. 
    }
    rewrite <- G. reflexivity.
  }
  {
    simpl. intro H. 
    assert (rev (rev l1' ++ rev [n]) = l2) as G.
    { rewrite -> rev_one_element, H, rev_involutive. reflexivity. }
    rewrite <- G. rewrite <- rev_app_distr, rev_involutive. reflexivity.
  }
Qed.

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Fixpoint nth' (l : natlist) (n : nat) : natoption := 
  match l with 
  | nil => None
  | h :: t => match beq_nat n 0 with 
              | true => Some h
              | false => nth' t (pred n)
              end
  end.

Example test_nth'_error1 : nth' [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth'_error2 : nth' [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth'_error3 : nth' [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

Fixpoint nth (l : natlist) (n : nat) : natoption :=
  match l with
  | nil => None
  | h :: t => if beq_nat n 0 
                then Some h
                else nth t (pred n)
  end.

Example test_nth_error1 : nth [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with 
  | None => d
  | Some n' => n'
  end.

Definition hd_error (l : natlist) : natoption :=
  match l with
  | [] => None
  | h::t => Some h
  end.

Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l : natlist) (default : nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros l default. induction l as [| n l' IHl']; reflexivity.
Qed.

End NatList.

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id (x1 x2 : id) :=
  match x1,x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall x, true = beq_id x x.
Proof.
  intros x.
  destruct x. simpl. apply NatList.beq_nat_refl.
Qed.

Module PartialMap.
Export NatList.

Inductive partial_map : Type :=
  | empty : partial_map
  | record : id -> nat -> partial_map -> partial_map. 

Fixpoint update (p : partial_map) (key : id) (n : nat) : partial_map :=
  record key n p.

Compute record (Id 5) 4 (record (Id 2) 3 empty).

Fixpoint find (key : id) (p : partial_map) : natoption :=
  match p with
  | empty => None
  | record key' val p' => if beq_id key key'
                           then Some val
                           else find key p'
  end.

Theorem beq_id_refl : forall (k : id), beq_id k k = true.
Proof.
  intros k. destruct k. simpl. rewrite <- beq_nat_refl. reflexivity.
Qed.

Theorem update_eq : forall (d : partial_map) (key : id) (v : nat),
  find key (update d key v) = Some v.
Proof.
  intros d k v. 
  destruct d; simpl; rewrite -> beq_id_refl; reflexivity.
Qed.

Theorem update_neq : forall (d : partial_map) (x y : id) (o : nat),
  beq_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros * H.
  destruct d; simpl; rewrite -> H; reflexivity.
Qed.

End PartialMap.

Compute double 3.
 
