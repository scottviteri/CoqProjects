(*
Set Warnings "-notation-overridde,-parsing".
*)
Require Export Lists.

Inductive boollist : Type :=
| bool_nil : boollist
| bool_cons : bool -> boollist -> boollist.

Inductive list (X : Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Check list.
Check (nil nat).
Check (cons nat 3 (nil nat)).
Check nil.
Check cons.

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => (cons X x (repeat X x count'))
  end.

Example test_repeat1 : 
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

Example test_repeat2 : 
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

Module MumbleGrumble.

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (X : Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

Check b a 5. (* mumble *)
Check d. (* forall X : Type, mumble -> grumble X *)
(* Check d (b a 5). expecting mumble type, not mumble element *)
Check d mumble (b a 5). (* grumble mumble *)
Check d bool (b a 5). (* grumble bool *)
Check e bool true. (* grumble bool *)
Check b c 0. (* mumble *)
Check e mumble (b c 0). (* grumble mumble *)
(* Check e bool (b c 0). expecting bool, gets mumble *)
Check c. (* mumble *)

End MumbleGrumble.

Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Check repeat'. (* forall X : Type, X -> nat -> list X *)
Check repeat.  (* same type *)

Definition list123' :=
  cons _ 1 ( cons _ 2 ( cons _ 3 (nil _))).

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with 
  | 0 => nil
  | S count' => cons x (repeat''' x count')
  end.

(* list' not good because now cannot say list' nat *)

Inductive list' {X : Type} : Type :=
  | nil' : list'
  | cons' : X -> list' -> list'.

(* Do the type inference at the function level, not the datatype level *)

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons h t => S (length t)
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = cons 2 (cons 1 nil).
Proof. reflexivity. Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

Fail Definition mynil := nil. (* cannot infer type here *)
Definition mynil : list nat := nil. (* enough info *)
Check @nil. (* force implicit to explicity *)
Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y) 
                      (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                      (at level 60, right associativity).

Definition list123''' := [1;2;3].

Theorem app_assoc : forall (X : Type),
  forall (l1 l2 l3 : list X), 
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros X l1 l2 l3.
  induction l1 as [| x l1' IHl1'].
  - reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem app_nil_r : forall (X : Type), 
 forall l : list X, l ++ [] = l.
Proof.
  intros X l. induction l as [| x l' IHl'].
  - reflexivity. 
  - simpl. rewrite -> IHl'. reflexivity.
Qed.

Theorem app_length : forall (X : Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2.
  induction l1 as [| x l1' IHl1'].
  - reflexivity.
  - simpl. rewrite <- IHl1'. reflexivity.
Qed.

Theorem rev_app_distr : forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2.
  induction l1 as [| x l1' IHl1'].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite <- app_assoc, IHl1'. reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l.
  induction l as [| x l' IHl'].
  - reflexivity.
  - simpl. rewrite -> rev_app_distr, IHl'. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
| pair: X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.
Notation "( x , y )" := (pair x y). (* element of pair type *)
Notation "X * Y" := (prod X Y) : type_scope. (* pair type *)

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x,y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with 
  | (x,y) => y
  end.

Fixpoint combine {X Y : Type} (l1 : list X) (l2 : list Y) : list (X*Y) :=
  match l1,l2 with
  | [],_ => []
  | _,[] => [] 
  | hx::tx, hy::ty  => cons (hx,hy) (combine tx ty)
  end.

Check @combine. (* forall X Y : Type, list X -> list Y -> list X * Y *)

Compute (combine [1;2] [false; false; true; true]).

Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X)*(list Y) :=
  match l with
  | [] => ([],[])
  | h::t => ( (fst h)::(fst (split t)), (snd h)::(snd (split t)) )
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

Inductive option (X : Type) : Type := 
  | Some : X -> option X
  | None : option X.

Arguments Some {X} _.
Arguments None {X}. Search beq_nat.

(*
Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
  match l with
  | [] => None
  | h::t => match n with
            | 0 => Some h
            | S n' => nth_error t n'
            end
  end.
*)

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
  match l with 
  | [] => None  
  | h::t => if (beq_nat 0 n) then Some h else nth_error t (pred n)
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | [] => None
  | h::t => Some h
  end.

Check @hd_error.
Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

Definition doit3times {X : Type} (f:X->X) (n:X) : X :=
  (f (f (f n))).

Check @doit3times.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

Fixpoint filter {X : Type} (test: X->bool) (l : list X) : list X :=
  match l with
  | [] => []
  | h :: t => if (test h) then (h :: (filter test t)) else (filter test t)
  end.

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.
Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.
Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition countoddmembers' (l : list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Example test_anon_fun' : doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2': filter (fun l => beq_nat (length l) 1) 
                              [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ] = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Compute (3 <= 4).

Fixpoint ble_nat (n m : nat) : bool :=
  match n with 
  | 0 => true
  | S n' => if (beq_nat m 0) then false else ble_nat n' (pred m)
  end.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => andb (ble_nat 8 n) (evenb n)) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Fixpoint partition {X : Type} (test: X -> bool) (l : list X) : list X * list X :=
  match l with
  | [] => ([],[])
  | h :: t => if test h then (h::(fst (partition test t)),(snd (partition test t)))
                        else ((fst (partition test t)), h::(snd (partition test t)))
  end.

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y: Type} (f:X->Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h)::(map f t)
  end.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Example test_map2:
  map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.

Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

Compute rev [1;2;3].

Theorem map_distr : forall (X Y: Type) (l1 l2 : list X) (f:X->Y), 
  (map f l1) ++ (map f l2) = (map f (l1 ++ l2)).
Proof.
  intros X Y l1 l2 f. induction l1 as [|n l1' IHl1'].
  - reflexivity.
  - simpl. rewrite <- IHl1'. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f:X->Y) (l:list X), 
  (map f (rev l)) = (rev (map f l)).
Proof.
  intros X Y f l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite <- IHl'. rewrite <- map_distr. reflexivity.
Qed.

Fixpoint flat_map {X Y : Type} (f:X->list Y) (l:list X) : list Y :=
  match l with 
  | [] => []
  | h :: t => f h ++ (flat_map f t)
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Fixpoint map_option {X Y : Type} (f:X->Y) (x : option X) : option Y :=
  match x with
  | None => None
  | Some n => Some (f n)
  end.

Fixpoint fold {X Y: Type} (f:X->Y->Y) (l : list X) (y : Y) : Y :=
  match l with 
  | [] => y
  | h :: t => f h (fold f t y)
  end.

Compute fold plus [1;2;3;4] 0.
Check (fold andb).

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.
Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.
Example fold_example3 :
  fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

Definition constfun {X : Type} (x : X): nat -> X :=
  fun n => x.

Definition ftrue := constfun true.
Check ftrue.
Compute ftrue 3.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.
Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Check plus. 

Definition plus3 := plus 3.

Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

Module Exercises.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.
Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall (X : Type) (l : list X),
  fold_length l = length l.
Proof. intros X l. induction l as [| n l' IHl'].
- reflexivity.
- simpl. rewrite <- IHl'. reflexivity.
Qed.

Definition fold_map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun x y => (f x) :: y) l [].

Theorem fold_map_correct : forall (X Y: Type) (f:X->Y) (l : list X),
  (map f l) = (fold_map f l).
Proof. 
  intros X Y f l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite -> IHl'. reflexivity.
Qed.

Definition prod_curry {X Y Z : Type} (f:(X*Y)->Z) (a:X) (b:Y) : Z := 
  f (a,b).
Definition prod_uncurry {X Y Z : Type} (f:X->Y->Z) (p:X*Y) : Z := 
  f (fst p) (snd p).

Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Check @prod_curry. (* : forall (X Y Z : Type), (X*Y->Z)->(X->Y->Z). *)
Check @prod_uncurry. (* : forall (X Y Z : Type), (X->Y->Z)->(X*Y->Z). *)

Theorem pair_parts : forall (X Y : Type) (p:X*Y), 
  (fst p, snd p) = p.
Proof.
  intros X Y p. destruct p. simpl. reflexivity.
Qed. 

Theorem uncurry_curry : forall (X Y Z : Type) (f:(X*Y)->Z) (p:X*Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p.
  unfold prod_curry, prod_uncurry. rewrite -> pair_parts. reflexivity.
Qed.

Module Church.
Definition nat := forall X : Type, (X -> X) -> X -> X.
Definition one : nat :=
  fun (X : Type) (f:X->X) (x:X) => f x.
Definition two : nat :=
  fun (X : Type) (f:X->X) (x:X) => f (f x).
Definition zero : nat :=
  fun (X : Type) (f:X->X) (x:X) => x.

Definition three : nat := @doit3times.

Definition succ (n : nat) : nat :=
  fun (X:Type) (f:X->X) (x:X) => f (n X f x).

Example succ_1 : succ zero = one.
Proof. reflexivity. Qed.
Example succ_2 : succ one = two.
Proof. reflexivity. Qed.
Example succ_3 : succ two = three.
Proof. reflexivity. Qed.

Definition plus (n m : nat) : nat :=
  fun (X : Type) (f:X->X) (x:X) => n X f (m X f x).

Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.
Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.
Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

Check fun n:nat => plus three n.
Compute succ (succ zero).
Compute (plus three) two.
Compute (plus three zero).
Compute (plus three).

Definition mult (n m : nat) : nat :=
  fun (X : Type) (f:X->X) (x:X) => n X (m X f) x.

Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.
Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.
Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.

Compute fun (X : Type) (f:X->X) => three X f.

End Church.
End Exercises.
