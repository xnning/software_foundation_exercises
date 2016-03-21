Require Export Induction.

Module NatList.

(* Pairs of Numbers *)

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

Check (pair 3 5).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Eval compute in (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Eval compute in (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall(n m:nat),
    (n, m) = (fst (n, m), snd (n, m)).
Proof.
  reflexivity. Qed.

Theorem surjective_pairing_stuck : forall(p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Abort.

Theorem surjective_pairing : forall(p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

(* Exercise: 1 star (snd_fst_is_swap) *)

Theorem snd_fst_is_swap : forall(p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

(* Exercise: 1 star, optional (fst_swap_is_snd) *)


Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.
