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

(* Falsehood *)

Inductive False : Prop := .

Theorem False_implies_nonsense :
  False -> 2 + 2 = 5.
Proof.
  intros contra.
  inversion contra. Qed.

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra. Qed.

Theorem ex_falso_quodlibet : forall(P:Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra. Qed.

(* Exercise: 2 stars, advanced (True) *)

Inductive True : Prop := tr.

(* Negation *)

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. inversion H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q H. destruct H as [HP HNA]. unfold not in HNA.
  apply HNA in HP. inversion HP. Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H. unfold not. intros G. apply G. apply H. Qed.

Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q HPQ.
  unfold not.
  intros HQ.
  intros HP.
  apply HQ. apply HPQ. apply HP.
Qed.

(* Exercise: 1 star (not_both_true_and_false) *)

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P.
  unfold not.
  intros HP.
  destruct HP as [L R].
  apply R. apply L.
Qed.

Theorem classic_double_neg : forall P : Prop,
 ~~P -> P.
Proof.
  intros P H. unfold not in H.
  Abort.

(* Exercise: 5 stars, advanced, optional (classical_axioms) *)

Definition peirce := forall P Q: Prop,
  ((P -> Q) -> P) -> P.
Definition classic := forall P:Prop,
  ~~P -> P.
Definition excluded_middle := forall P:Prop,
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P \/ Q.
Definition implies_to_or := forall P Q:Prop,
  (P -> Q) -> (~ P \/ Q).

Theorem equiv_peirce_classic : peirce <-> classic.
Proof.
  split.
  Case "->".
    unfold peirce. unfold classic. unfold not.
    intros H. intros P. intros h.
    apply H with (Q:=False).
    intros h2.
    apply h in h2.
    inversion h2.
  Case "<-".
    unfold classic. unfold peirce. unfold not.
    intros H. intros P Q. intros h1.
    apply H.
    intros h2.
    apply h2.
    apply h1.
    intros p.
    apply h2 in p.
    inversion p.
Qed.

Theorem equiv_classic_excluded_middle : classic <-> excluded_middle.
Proof.
  split.
  Case "->".
    unfold classic. unfold excluded_middle.
    intros H. intros P.
    apply H.
    unfold not.
    intros h.
    apply h.
    right.
    intros p.
    apply h.
    left. apply p.
  Case "<-".
    unfold excluded_middle. unfold classic.
    intros H. intros P.
    unfold not.
    intros h.
    destruct (H P) as [p | notp].
    apply p.
    unfold not in notp.
    apply h in notp.
    inversion notp.
Qed.

Theorem equiv_exclued_middle_de_morgan_not_and_not :
  excluded_middle <-> de_morgan_not_and_not.
Proof.
  unfold excluded_middle. unfold de_morgan_not_and_not.
  split.
  Case "->".
    intros H. intros P Q. intros h.
    destruct (H P) as [p | notp].
    SCase "p". left. apply p.
    SCase "notp".
      destruct (H Q) as[q | notq].
      SSCase "q". right. apply q.
      SSCase "notq". assert (~P /\ ~Q). split. apply notp. apply notq.
        apply h in H0. inversion H0.
  Case "<-".
    intros H. intros P.
    apply H.
    unfold not.
    intros h.
    destruct h as [l r].
    apply r in l.
    inversion l.
Qed.

Theorem equiv_de_morgan_not_and_not_implies_to_or :
  de_morgan_not_and_not <-> implies_to_or.
Proof.
  split.
  Case "->".
    unfold de_morgan_not_and_not. unfold implies_to_or.
    intros H. intros P Q. intros h.
    apply H. unfold not.
    intros h1.
    destruct h1 as [l r].
    apply l. intros p. apply r. apply h. apply p.
  Case "<-".
    unfold de_morgan_not_and_not. unfold implies_to_or.
    intros H. intros P Q. intros h.
    destruct (H P P) as [notp | p]. apply iff_refl.
      SCase "notp".
        destruct (H Q Q) as [notq | q]. apply iff_refl.
        SSCase "notq". assert (~P /\ ~Q). split. apply notp. apply notq.
          apply h in H0. inversion H0.
        SSCase "q". right. apply q.
      SCase "p". left. apply p.
Qed.

Theorem equiv_not_implies_to_or_peirce :
  implies_to_or <-> peirce.
Proof.
  split.
  Case "->".
    unfold implies_to_or. unfold peirce.
    intros H. intros P Q.
    intros h.
    assert (~ P \/ P). apply H. apply iff_refl.
    destruct H0 as [notp | p].
    SCase "notp".
      assert (P -> Q). intros p. apply notp in p. inversion p.
      apply h. apply H0.
    SCase "p". apply p.
  Case "<-".
    unfold implies_to_or. unfold peirce.
    intros H. intros P Q. intros h.
    apply H with (Q:=False).
    intros h1.
    assert (P -> False). intros p. apply h1. right. apply h. apply p.
    left.  unfold not. apply H0.
Qed.

(* Exercise: 3 stars (excluded_middle_irrefutable) *)

Theorem excluded_middle_irrefutable: forall (P:Prop), ~ ~ (P \/ ~ P).
Proof.
  intros P.
  unfold not.
  intros h.
  apply h.
  right.
  intros p.
  apply h. left. apply p.
Qed.

Notation "x <> y" := (~ (x = y)) : type_scope.

Theorem not_false_then_true : forall b : bool,
  b <> false -> b = true.
Proof.
  intros b H. destruct b.
  Case "b = true". reflexivity.
  Case "b = false".
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity. Qed.

(* Exercise: 2 stars (false_beq_nat) *)
Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof.
  intros n.
  induction n as [ |n'].
  Case "n = 0".
    intros m h.
    destruct m as [ |m'].
    unfold not in h. apply ex_falso_quodlibet. apply h. reflexivity.
    simpl. reflexivity.
  Case "n = S n'".
    intros m h.
    destruct m as [| m'].
    simpl. reflexivity.
    unfold not in h. simpl. apply IHn'. unfold not.
      intros h2. apply h. apply f_equal. apply h2.
Qed.

Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
  intros n m h.
  unfold not.
  intros nm.
  rewrite nm in h.
  rewrite <- beq_nat_refl in h.
  inversion h.
Qed.
