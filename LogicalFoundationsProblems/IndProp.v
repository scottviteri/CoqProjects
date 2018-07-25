Set Warnings "-notation-overriden,-parsing".

Require Export Logic.
Require Coq.omega.Omega.


(* CIC built from function types and inductive types *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS : forall m:nat, ev m -> ev (S (S m)).

Theorem ev_4 : ev 4.
Proof. apply ev_SS,ev_SS,ev_0. Qed.

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4 : 
  forall n, ev n -> ev (4 + n).
Proof.
  intros n H. apply ev_SS, ev_SS. assumption.
Qed.

Definition double (n : nat) : nat :=
  plus n n.
Compute double 3.

Definition pred (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => n'
  end.

Theorem ev_double : forall n, ev (double n).
Proof.
  intros n. unfold double. induction n.
  - apply ev_0.
  - simpl. rewrite <- plus_comm. simpl.
    apply ev_SS. apply IHn.
Qed.

Theorem ev_minus2 : forall n, ev n -> ev (pred (pred n)).
Proof.
  intros n E. inversion E as [| n' E'].
  - simpl. apply ev_0.
  - simpl. apply E'.
Qed.

Theorem ev_minus2' : forall n, ev n -> ev (pred (pred n)).
Proof.
  intros n E. destruct E.
  - simpl. apply ev_0.
  - simpl. apply E.
Qed.

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n H. inversion H as [| m h1 h2]. apply h1.
Qed.

Theorem one_not_even : not (ev 1).
Proof. intros H. inversion H. Qed.

Theorem SSSSev__even: forall n, ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H. inversion H as [| m H1 H2].
  apply evSS_ev in H1. apply H1.
Qed.

Theorem even5_nonsense : ev 5 -> 2 + 2 = 9.
Proof.
  intros H. simpl. inversion H as [| n' E H1].
  inversion E as [| n'' E' H2]. inversion E'.
Qed.

(*
Check eq.
Print eq_symm.
Theorem eq_symm :  

Lemma ev_even_firsttry :  n,
  ev n -> exists k, n = double k.
Proof.
  intros n E. inversion E as [| n' E'].
  - exists 0. reflexivity.
  - assert (I : (exists k', double k' = n') ->
                (exists k, double k = S (S n'))).
    { intros [k' Hk']. rewrite <- Hk'. exists (S k').
      unfold double. simpl. rewrite -> plus_comm. simpl. reflexivity. }
  Search eq. rewrite -> eq_Symmetric.
*)

Lemma add_S : forall n m: nat, n = m -> S n = S m.
Proof. intros n m E. rewrite E. reflexivity. Qed.

Lemma remove_S : forall n m:nat, S n = S m -> n = m.
Proof. intros n m E. inversion E. reflexivity. Qed.

Lemma succ_even : forall k:nat, double (S k) = S (S (double k)).
Proof.
  intros k. unfold double.
  simpl. apply add_S. apply plus_comm.
Qed.

Lemma ev_even : forall n, ev n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  { exists 0. reflexivity. }
  { destruct IH as [k' Hk']. rewrite Hk'.
    exists (S k'). apply eq_sym. apply succ_even.
  }
Qed.

(* when to use indprop and when to use decidable definition? *)
(* maybe indprop more general? I think this is true *)

Lemma rev_SS : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n H. inversion H. assumption.
Qed.

Lemma exists_half_to_ev : forall n, ((exists k, n = double k) -> ev n).
Proof.
  intros n [k H]. rewrite H. clear H. induction k.
  { apply ev_0. } { rewrite succ_even. apply ev_SS. apply IHk. }
Qed.

Theorem ev_even_iff : forall n,
 ev n <-> exists k, n = double k.
Proof.
  intros n. split.
  { apply ev_even. }
  { apply exists_half_to_ev. }
Qed.

(* pose v assert? *)
(* assert adds to subgoals, 
   pose creates definition maybe *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m En Em.
  induction En as [|n' _ IH].
  { simpl. apply Em. }
  { simpl. apply ev_SS. apply IH. }
Qed.

Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum : forall n m, ev' n -> ev' m -> ev' (n + m).


(* one disjuntive branch for each contructor *)

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n. split.
  { intros Ev'_n. induction Ev'_n as [| | m m' Ev'_m IHEv_m Ev'_m' IHEv_m'].
    { apply ev_0. } 
    { apply ev_SS, ev_0. } 
    { apply ev_sum. { apply IHEv_m. } { apply IHEv_m'. }}
  }
  { intros Ev_n. induction Ev_n as [| n' Ev_n' IHEv'_n'].
    { apply ev'_0. } 
    { replace (S (S n')) with (2 + n').
      { apply ev'_sum. { apply ev'_2. } { apply IHEv'_n'. } }
      { reflexivity. }
    }
  }
Qed.

Theorem ev_ev__ev : forall n m, 
  ev (n + m) -> ev n -> ev m.
Proof.
  intros n m Ev_nm Ev_n.
  induction Ev_n as [| n' Ev_n' IH]. 
  { simpl in Ev_nm; assumption. }
  { simpl in Ev_nm. apply rev_SS in Ev_nm.
    apply IH. apply Ev_nm.
  }
Qed.

(*
Theorem ev_plus_plus : forall n m p, 
  ev (n + m) -> ev (n + p) -> ev (m + p).
Proof.
  intros n m p E_nm E_np.
  assert (H := forall n m : (ev n -> ev m)).
 *) 
