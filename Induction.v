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
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
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

(* More Exercises *)

(* Exercise: 3 stars, optional (more_exercises) *)

Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
Proof.
  intros n.
  induction n.
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite <- IHn.
    reflexivity.
Qed.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b.
  destruct b.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat, 
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  intros n m p. intros h.
  induction p as [ | p'].
  rewrite -> plus_O_n.
  rewrite -> plus_O_n.
  rewrite -> h.
  reflexivity.
  simpl.
  rewrite -> IHp'.
  reflexivity.
Qed.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  simpl. reflexivity.
Qed.


Theorem mult_1_l : forall n:nat, 1 × n = n.
Proof.
  intros n.
  simpl. 
  rewrite -> plus_O_r.
  reflexivity.
Qed.


Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  intros b c.
  destruct b.
  simpl.
  assert (h1: orb c (negb c) = true).
    Case "assert h1: orb c (negb c) = true".
    destruct c.
    simpl. reflexivity.
    simpl. reflexivity.
  rewrite -> h1. reflexivity.
  simpl.
  reflexivity.
Qed.

Theorem plus_swap_num: forall a b c d: nat,
    (a + b) + (c + d) = (a + c) + (b + d).
Proof.
  intros a b c d.
  induction a  as [ | a'].
  simpl.
  rewrite -> plus_swap.
  reflexivity.
  simpl.
  rewrite -> IHa'.
  reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) × p = (n × p) + (m × p).
Proof.
  intros n m p.
  induction p as [ | p'].
  rewrite -> mult_0_r.
  rewrite -> mult_0_r.
  rewrite -> mult_0_r.
  reflexivity.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_Sm.
  rewrite -> IHp'.
  rewrite -> plus_swap_num.
  reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n × (m × p) = (n × m) × p.
Proof.
  intros n m p.
  induction n as [ |n'].
  rewrite -> mult_0_l.
  rewrite -> mult_0_l.
  reflexivity.
  simpl.
  rewrite -> IHn'.
  rewrite -> mult_plus_distr_r.
  reflexivity.
Qed.

(* Exercise: 2 stars, optional (beq_nat_refl) *)

Theorem beq_nat_refl : forall n : nat, 
  true = beq_nat n n.
Proof.
  intros n.
  induction n as [ | n'].
  simpl. reflexivity.
  simpl. rewrite -> IHn'.
  reflexivity.
Qed.

(* Exercise: 2 stars, optional (plus_swap') *)
Theorem plus_swap' : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  replace (n+m) with (m+n).
  reflexivity.
  rewrite -> plus_comm.
  reflexivity.
Qed.

(* Exercise: 3 stars (binary_commute) *)

Theorem bin_to_nat_pres_incr: forall n:bin,
    bin_to_nat (incr n) = bin_to_nat n + 1.
Proof.
  intros n.
  induction n as [ | nt | nmt].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = 2 * nt".
    simpl.
    rewrite -> plus_O_r.
    reflexivity.
  Case "n = 2 * nmt + 1".
    simpl.
    rewrite -> plus_O_r.
    rewrite -> plus_O_r.
    rewrite -> IHnmt.
    rewrite -> plus_swap.
    rewrite -> plus_assoc.
    rewrite -> plus_assoc.
    reflexivity.
Qed.

(* Exercise: 5 stars, advanced (binary_inverse) *)

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
  | 0 => Z
  | S n' => incr (nat_to_bin n')
  end.

Theorem nat_to_bin_to_nat : forall n:nat,
    n = (bin_to_nat (nat_to_bin n)).
Proof.
  intros n.
  induction n as [ | n'].
  Case "n = 0".
    simpl.
    reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> bin_to_nat_pres_incr.
    rewrite <- IHn'.
    rewrite -> plus_comm.
    rewrite -> (plus_1_l n').
    reflexivity.
Qed.

(* (b) Because a number can have multiple forms of bin. For example, 0 can be Z, or can be (T Z). *)

Fixpoint normalize (b:bin) : bin :=
  match b with
  | Z => Z
  | T b' => match (normalize b') with
             | Z => Z
             | x' => T x'
           end
  | MT b' => MT (normalize b')
  end.

Theorem bin_nat_bin : forall b:bin,
    (nat_to_bin (bin_to_nat b)) = normalize b.
Proof.
  Abort.
