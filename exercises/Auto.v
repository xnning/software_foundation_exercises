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

Ltac rwinv H1 H2 := rewrite H1 in H2; inv H2.

Theorem ceval_deterministic'': forall c st st1 st2,
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
      rwinv H H5.
  Case "E_IfFalse".
    SCase "b evaluates to true (contradiction)".
      rwinv H H5.
  Case "E_WhileEnd".
    SCase "b evaluates to true (contradiction)".
      rwinv H H2.
  Case "E_WhileLoop".
    SCase "b evaluates to false (contradiction)".
      rwinv H H4.
    SCase "b evaluates to true".
      assert (st' = st'0) as EQ1.
        SSCase "Proof of assertion". auto.
      subst st'0.
      auto. Qed.

Ltac find_rwinv :=
  match goal with
    H1: ?E = true, H2: ?E = false |- _ => rwinv H1 H2
  end.

Theorem ceval_deterministic''': forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  ceval_cases (induction E1) Case;
           intros st2 E2; inv E2; try find_rwinv; auto.
  Case "E_Seq".
    assert (st' = st'0) as EQ1.
      SCase "Proof of assertion". auto.
    subst st'0.
    auto.
  Case "E_WhileLoop".
    SCase "b evaluates to true".
      assert (st' = st'0) as EQ1.
        SSCase "Proof of assertion". auto.
      subst st'0.
      auto. Qed.

Theorem ceval_deterministic'''': forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  ceval_cases (induction E1) Case;
           intros st2 E2; inv E2; try find_rwinv; auto.
  Case "E_Seq".
    rewrite (IHE1_1 st'0 H1) in *. auto.
  Case "E_WhileLoop".
    SCase "b evaluates to true".
      rewrite (IHE1_1 st'0 H3) in *. auto. Qed.

Ltac find_eqn :=
  match goal with
    H1: forall x, ?P x -> ?L = ?R, H2: ?P ?X |- _ =>
         rewrite (H1 X H2) in *
  end.

Theorem ceval_deterministic''''': forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  ceval_cases (induction E1) Case;
           intros st2 E2; inv E2; try find_rwinv; repeat find_eqn; auto.
  Qed.

Module Repeat.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE"
  | Case_aux c "CRepeat" ].

Notation "'SKIP'" :=
  CSkip.
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'REPEAT' e1 'UNTIL' b2 'END'" :=
  (CRepeat e1 b2) (at level 80, right associativity).

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      ceval st SKIP st
  | E_Ass  : forall st a1 n X,
      aeval st a1 = n ->
      ceval st (X ::= a1) (update st X n)
  | E_Seq : forall c1 c2 st st' st'',
      ceval st c1 st' ->
      ceval st' c2 st'' ->
      ceval st (c1 ; c2) st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      ceval st c2 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      ceval st (WHILE b1 DO c1 END) st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st' (WHILE b1 DO c1 END) st'' ->
      ceval st (WHILE b1 DO c1 END) st''
  | E_RepeatEnd : forall st st' b1 c1,
      ceval st c1 st' ->
      beval st' b1 = true ->
      ceval st (CRepeat c1 b1) st'
  | E_RepeatLoop : forall st st' st'' b1 c1,
      ceval st c1 st' ->
      beval st' b1 = false ->
      ceval st' (CRepeat c1 b1) st'' ->
      ceval st (CRepeat c1 b1) st''
.

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass"
  | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop"
  | Case_aux c "E_RepeatEnd" | Case_aux c "E_RepeatLoop"
].

Notation "c1 '/' st '||' st'" := (ceval st c1 st')
                                 (at level 40, st at level 39).

Theorem ceval_deterministic: forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  ceval_cases (induction E1) Case;
           intros st2 E2; inv E2; try find_rwinv; repeat find_eqn; auto.
  Case "E_RepeatEnd".
    SCase "b evaluates to false (contradiction)".
       find_rwinv.
       (* oops: why didn't [find_rwinv] solve this for us already?
          answer: we did things in the wrong order. *)
  case "E_RepeatLoop".
     SCase "b evaluates to true (contradiction)".
        find_rwinv.
Qed.

Theorem ceval_deterministic': forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  ceval_cases (induction E1) Case;
           intros st2 E2; inv E2; repeat find_eqn; try find_rwinv; auto.
Qed.

End Repeat.
