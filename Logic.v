Require Export MoreCoq.

(* Propositions *)

Check (3 = 3).
(* ===> Prop *)

Check (forall(n:nat), n = 2).
(* ===> Prop *)

(* Proofs and Evidence *)

Lemma silly : 0 × 3 = 0.
Proof. reflexivity. Qed.

Print silly.

Lemma silly_implication : (1 + 1) = 2 -> 0 × 3 = 0.
Proof. intros H. reflexivity. Qed.

Print silly_implication.

(* Conjunction (Logical "and") *)

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q) : type_scope .

Check conj.

Theorem and_example :
  (0 = 0) /\ (4 = mult 2 2).
Proof.
  apply conj.
  Case "left". reflexivity.
  Case "right". reflexivity. Qed.

Theorem and_example' :
  (0 = 0) /\ (4 = mult 2 2).
Proof.
  split.
    Case "left". reflexivity.
    Case "right". reflexivity. Qed.

Theorem proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q H.
  destruct H as [HP HQ].
  apply HP. Qed.

(* Exercise: 1 star, optional (proj2) *)

Theorem proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q H.
  destruct H as [HP HQ].
  apply HQ. Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  (* WORKED IN CLASS *)
  intros P Q H.
  destruct H as [HP HQ].
  split.
    Case "left". apply HQ.
    Case "right". apply HP. Qed.

(* Exercise: 2 stars (and_assoc) *)

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  destruct H as [HP [HQ HR]].
  split. split.
  apply HP. apply HQ. apply HR.
Qed.

(* Iff *)
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

Theorem iff_implies : forall P Q : Prop,
  (P <-> Q) -> P -> Q.
Proof.
  intros P Q H.
  destruct H as [HAB HBA]. apply HAB. Qed.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q H.
  destruct H as [HAB HBA].
  split.
    Case "→". apply HBA.
    Case "←". apply HAB. Qed.

(* Exercise: 1 star, optional (iff_properties) *)

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros P.
  split.
  intros p. apply p.
  intros p. apply p.
Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R.
  intros PQ.
  intros QR.
  inversion PQ.
  inversion QR.
  split.
  Case "P -> R". intros p. apply H1. apply H. apply p.
  Case "R -> P". intros r. apply H0. apply H2. apply r.
Qed.
