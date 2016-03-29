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

(* Disjunction (Logical "or") *)

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.

Check or_introl.

Check or_intror.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  destruct H as [HP | HQ].
    Case "left". apply or_intror. apply HP.
    Case "right". apply or_introl. apply HQ. Qed.

Theorem or_commut' : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  destruct H as [HP | HQ].
    Case "left". right. apply HP.
    Case "right". left. apply HQ. Qed.

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. intros H. destruct H as [HP | [HQ HR]].
    Case "left". split.
      SCase "left". left. apply HP.
      SCase "right". left. apply HP.
    Case "right". split.
      SCase "left". right. apply HQ.
      SCase "right". right. apply HR. Qed.

(* Exercise: 2 stars (or_distributes_over_and_2) *)

Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R H.
  destruct H as [[HP1 | HQ] [HP2 | HR]].
  Case "P P". left. apply HP1.
  Case "P R". left. apply HP1.
  Case "Q P". left. apply HP2.
  Case "Q R". right. split. apply HQ. apply HR.
Qed.

(* Exercise: 1 star, optional (or_distributes_over_and) *)

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  Case "left -> right". apply or_distributes_over_and_1.
  Case "right -> left". apply or_distributes_over_and_2.
Qed.

Theorem andb_prop : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
    Case "b = true". destruct c.
      SCase "c = true". apply conj. reflexivity. reflexivity.
      SCase "c = false". inversion H.
    Case "b = false". inversion H. Qed.

Theorem andb_true_intro : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  intros b c H.
  destruct H.
  rewrite H. rewrite H0. reflexivity. Qed.

(* Exercise: 2 stars, optional (andb_false) *)

Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof.
  intros b c H.
  destruct b eqn:hb.
    destruct c eqn:hc.
    inversion H. right. reflexivity.
  left. reflexivity.
Qed.

(* Exercise: 2 stars, optional (orb_false) *)

Theorem orb_prop : forall b c,
  orb b c = true -> b =  true \/ c = true.
Proof.
  intros b c h.
  destruct b eqn:hb.
    left. reflexivity.
    destruct c eqn:hc.
      right. reflexivity.
      inversion h.
Qed.

(* Exercise: 2 stars, optional (orb_false_elim) *)

Theorem orb_false_elim : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof.
  intros b c h.
  destruct b eqn:hb.
    inversion h.
    destruct c eqn:hc.
      inversion h.
      split. reflexivity. reflexivity.
Qed.
