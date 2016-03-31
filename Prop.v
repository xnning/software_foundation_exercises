Require Export Logic.

(* Inductively Defined Propositions *)

(* a function. given nat. return Prop.  *)
Definition even (n:nat) : Prop :=
  evenb n = true.

(* a family of propositions "indexed by" natural numbers. *)
Inductive ev : nat -> Prop :=
    (* evidence for 0 is even *)
  | ev_0 : ev O
    (* evidence for S (S n) is even by giving evidence for n *)
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

(* Exercise: 1 star (double_even) *)
Theorem double_even : forall n,
  ev (double n).
Proof.
  induction n as [| n'].
  simpl. apply ev_0.
  simpl. apply (ev_SS (double n') IHn').
Qed.

(* Exercise: 1 star (varieties_of_beauty) *)
(* infinite since we have 0 *)

Inductive beautiful : nat -> Prop :=
  b_0 : beautiful 0
| b_3 : beautiful 3
| b_5 : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).

Theorem three_is_beautiful: beautiful 3.
Proof.
   apply b_3.
Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
   apply b_sum with (n:=3) (m:=5).
   apply b_3.
   apply b_5.
Qed.

Theorem beautiful_plus_eight: forall n, beautiful n -> beautiful (8+n).
Proof.
  intros n B.
  apply b_sum with (n:=8) (m:=n).
  apply eight_is_beautiful.
  apply B.
Qed.

(* Exercise: 2 stars (b_times2) *)
Theorem b_times2: forall n, beautiful n -> beautiful (2×n).
Proof.
  intros n B.
  simpl.
  apply b_sum with (n:=n) (m:=n+0).
  apply B. apply b_sum with (n:=n) (m:=0). apply B. apply b_0.
Qed.

(* Exercise: 3 stars (b_timesm) *)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m×n).
Proof.
  intros n m B.
  induction m as [| m'].
  simpl. apply b_0.
  simpl. apply b_sum. apply B. apply IHm'.
Qed.
