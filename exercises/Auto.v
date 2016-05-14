Require Export Imp.


Ltac inv H := inversion H; subst; clear H.

Theorem ceval_deterministic: forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  ceval_cases (induction E1) Case;
           intros st2 E2; inv E2.
  Case "E_Skip". reflexivity.
  Case "E_Ass". reflexivity.
  Case "E_Seq".
    assert (st' = st'0) as EQ1.
      SCase "Proof of assertion". apply IHE1_1; assumption.
    subst st'0.
    apply IHE1_2. assumption.
  Case "E_IfTrue".
    SCase "b evaluates to true".
      apply IHE1. assumption.
    SCase "b evaluates to false (contradiction)".
      rewrite H in H5. inversion H5.
  Case "E_IfFalse".
    SCase "b evaluates to true (contradiction)".
      rewrite H in H5. inversion H5.
    SCase "b evaluates to false".
      apply IHE1. assumption.
  Case "E_WhileEnd".
    SCase "b evaluates to false".
      reflexivity.
    SCase "b evaluates to true (contradiction)".
      rewrite H in H2. inversion H2.
  Case "E_WhileLoop".
    SCase "b evaluates to false (contradiction)".
      rewrite H in H4. inversion H4.
    SCase "b evaluates to true".
      assert (st' = st'0) as EQ1.
        SSCase "Proof of assertion". apply IHE1_1; assumption.
      subst st'0.
      apply IHE1_2. assumption.  Qed.

(* The auto and eauto tactics *)

Example auto_example_1 : forall (P Q R: Prop), (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2.  apply H1. assumption.
Qed.

Example auto_example_1' : forall (P Q R: Prop), (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  auto.
Qed.

Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P->Q) -> (P->S)) ->
  T ->
  P ->
  U.
Proof. auto. Qed.

Example auto_example_3 : forall (P Q R S T U: Prop),
                           (P -> Q) -> (Q -> R) -> (R -> S) ->
                           (S -> T) -> (T -> U) -> P -> U.
Proof.
  auto. (* When it cannot solve the goal, does nothing! *)
  auto 6.  (* Optional argument says how deep to search (default depth is 5) *)
Qed.

Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof.
  auto. Qed.

Example auto_example_5: 2 = 2.
Proof.
  Info 1 auto.  (* subsumes reflexivity because eq_refl is in hint database *)
Qed.

Require Coq.omega.Omega.
Ltac omega := Coq.omega.Omega.omega.

Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof. intros. omega. Qed.

Example auto_example_6 : forall n m p : nat,
  (n<= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  intros.
  auto. (* does nothing: auto doesn't destruct hypotheses! *)
  auto using le_antisym.
Qed.

Hint Resolve le_antisym.

Example auto_example_6' : forall n m p : nat,
  (n<= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  intros.
  auto. (* picks up hint from database *)
Qed.

Definition is_fortytwo x := x = 42.

Example auto_example_7: forall x, (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto.  (* does nothing *)
Abort.

Hint Unfold is_fortytwo.

Example auto_example_7' : forall x, (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  Info 1 auto.
Qed.

Hint Constructors ceval.

Definition st12 := update (update empty_state X 1) Y 2.
Definition st21 := update (update empty_state X 2) Y 1.

Example auto_example_8 : exists s',
  (IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI) / st21 || s'.
Proof.
  eexists. Info 1 auto.
Qed.

Example auto_example_8' : exists s',
  (IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI) / st12 || s'.
Proof.
  eexists. Info 1 auto.
Qed.

Theorem ceval_deterministic': forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  ceval_cases (induction E1) Case;
           intros st2 E2; inv E2; auto.
  Case "E_Seq".
    assert (st' = st'0) as EQ1.
      SCase "Proof of assertion". auto.
    subst st'0.
    auto.
  Case "E_IfTrue".
    SCase "b evaluates to false (contradiction)".
      rewrite H in H5. inversion H5.
  Case "E_IfFalse".
    SCase "b evaluates to true (contradiction)".
      rewrite H in H5. inversion H5.
  Case "E_WhileEnd".
    SCase "b evaluates to true (contradiction)".
      rewrite H in H2. inversion H2.
  Case "E_WhileLoop".
    SCase "b evaluates to false (contradiction)".
      rewrite H in H4. inversion H4.
    SCase "b evaluates to true".
      assert (st' = st'0) as EQ1.
        SSCase "Proof of assertion". auto.
      subst st'0.
      auto.
Qed.

Theorem ceval_deterministic'_alt: forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof with auto.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  ceval_cases (induction E1) Case;
           intros st2 E2; inv E2...
  Case "E_Seq".
    assert (st' = st'0) as EQ1.
      SCase "Proof of assertion"...
    subst st'0...
  Case "E_IfTrue".
    SCase "b evaluates to false (contradiction)".
      rewrite H in H5. inversion H5.
  Case "E_IfFalse".
    SCase "b evaluates to true (contradiction)".
      rewrite H in H5. inversion H5.
  Case "E_WhileEnd".
    SCase "b evaluates to true (contradiction)".
      rewrite H in H2. inversion H2.
  Case "E_WhileLoop".
    SCase "b evaluates to false (contradiction)".
      rewrite H in H4. inversion H4.
    SCase "b evaluates to true".
      assert (st' = st'0) as EQ1.
        SSCase "Proof of assertion"...
      subst st'0...
Qed.
