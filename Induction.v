(* Nameing Cases *)

Require Export Basics.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true". (* <----- here *)
    reflexivity.
  Case "b = false". (* <---- and here *)
    rewrite <- H.
    reflexivity.
Qed.

(* Exercise: 2 stars (andb_true_elim2) *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
  Case "c = true".
    reflexivity.
  Case "c = false".
    destruct b.
    SCase "b = true".
      rewrite <- H.
      reflexivity.
    SCase "b = false".
      rewrite <- H.
      reflexivity.
Qed.

(* Proof by Induction *)

Theorem plus_O_r : forall n:nat, n + O = n.

Proof.
  intros n.
  induction n as [ | n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
  Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [ | n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity. Qed.

(* Exercise: 2 stars (basic_induction) *)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as  [ | n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.
    
Theorem plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [ | n'].
  Case "n = 0".
    rewrite -> (plus_O_n m).
    rewrite -> (plus_O_n (S m)).
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [ | n'].
  Case "n = 0".
    rewrite -> (plus_O_n).
    rewrite -> (plus_O_r).
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite <- plus_n_Sm.
    rewrite -> IHn'.
    reflexivity.
  Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [ | n'].
  Case "n = 0".
    rewrite -> plus_O_n.
    rewrite -> (plus_O_n m).
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

(* Exercise: 2 stars (double_plus) *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n.
  induction n as [ | n'].
  Case "n = 0".
    simpl.
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.

(* Proofs Within Proofs *)

Theorem mult_O_plus' : forall n m :nat,
    ( 0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H : 0 + n = n).
    Case "assertion proof". reflexivity.
  rewrite -> H.
  reflexivity.
Qed.
  
Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  rewrite -> (plus_comm m n).
  reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    Case "Proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H. reflexivity. Qed.

(* Exercise: 4 stars (mult_comm) *)

Theorem plus_swap : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (Hl: n + (m + p) = (n + m) + p).
    Case "assertion: n + (m + p) = (n + m) + p".
    rewrite -> plus_assoc.
    reflexivity.
  assert (Hr: m + (n + p) = (m + n) + p).
    Case "assertion: m + (n + p) = (m + n) + p".
    rewrite -> plus_assoc.
    reflexivity.
  rewrite -> Hl.
  rewrite -> Hr.
  assert (H: n + m = m + n).
    Case "assertion: n + m = m + n".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H.
  reflexivity.
  Qed.

Theorem mult_O_r : forall n: nat, n * 0 = 0.
Proof.
  intros n.
  induction n as [ | n'].
  Case "n = 0".
    reflexivity.
  Case "n = n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem mult_Sn_m : forall m n: nat,
    m * (S n) = m + m * n.
Proof.
  intros m n.
  induction m as [| m'].
  Case "m = 0".
    simpl.
    reflexivity.
  Case "m = S m'".
    simpl.
    rewrite -> IHm'.
    rewrite -> plus_swap.
    reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
  intros m n.
  induction m as [ | m'].
  Case "m = 0".
    simpl.
    rewrite -> mult_O_r.
    reflexivity.
  Case "m = S m'".
    simpl.
    rewrite -> IHm'.
    rewrite -> mult_Sn_m.
    reflexivity.
Qed.


(* Exercise: 2 stars, optional (evenb_n__oddb_Sn) *)

Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  intros n.
  induction n as [ | n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    assert (H1: evenb (S (S n')) = evenb n').
      SCase "assertion: H1: evenb (S (S n')) = evenb n'".
      simpl. reflexivity.
    rewrite -> H1.
    rewrite <- (negb_involutive (evenb (S n'))).
    rewrite <- IHn'.
    reflexivity.
Qed.

    
      
    

  

