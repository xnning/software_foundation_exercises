Require Export SfLib.

(* Arithmetic and Boolean Expressions *)

Module AExp.

  Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

  Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

  Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2  => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

  Example test_aeval1:
    aeval (APlus (ANum 2) (ANum 2)) = 4.
  Proof. reflexivity. Qed.

  Fixpoint beval (b : bexp) : bool :=
    match b with
    | BTrue       => true
    | BFalse      => false
    | BEq a1 a2   => beq_nat (aeval a1) (aeval a2)
    | BLe a1 a2   => ble_nat (aeval a1) (aeval a2)
    | BNot b1     => negb (beval b1)
    | BAnd b1 b2  => andb (beval b1) (beval b2)
    end.

  Fixpoint optimize_0plus (a:aexp) : aexp :=
    match a with
    | ANum n =>
      ANum n
    | APlus (ANum 0) e2 =>
      optimize_0plus e2
    | APlus e1 e2 =>
      APlus (optimize_0plus e1) (optimize_0plus e2)
    | AMinus e1 e2 =>
      AMinus (optimize_0plus e1) (optimize_0plus e2)
    | AMult e1 e2 =>
      AMult (optimize_0plus e1) (optimize_0plus e2)
    end.

  Example test_optimize_0plus:
    optimize_0plus (APlus (ANum 2)
                          (APlus (ANum 0)
                                 (APlus (ANum 0) (ANum 1))))
    = APlus (ANum 2) (ANum 1).
  Proof. reflexivity. Qed.

  Theorem optimize_0plus_sound: forall a,
      aeval (optimize_0plus a) = aeval a.
  Proof.
    intros a. induction a.
    Case "ANum". reflexivity.
    Case "APlus". destruct a1.
      SCase "a1 = ANum n". destruct n.
        SSCase "n = 0".  simpl. apply IHa2.
        SSCase "n <> 0". simpl. rewrite IHa2. reflexivity.
      SCase "a1 = APlus a1_1 a1_2".
        simpl. simpl in IHa1. rewrite IHa1.
        rewrite IHa2. reflexivity.
      SCase "a1 = AMinus a1_1 a1_2".
        simpl. simpl in IHa1. rewrite IHa1.
        rewrite IHa2. reflexivity.
      SCase "a1 = AMult a1_1 a1_2".
        simpl. simpl in IHa1. rewrite IHa1.
        rewrite IHa2. reflexivity.
    Case "AMinus".
      simpl. rewrite IHa1. rewrite IHa2. reflexivity.
    Case "AMult".
      simpl. rewrite IHa1. rewrite IHa2. reflexivity.  Qed.

(* Coq Automation *)

 Theorem ev100 : ev 100.
 Proof.
   repeat (apply ev_SS). (* applies ev_SS 50 times,
                           until [apply ev_SS] fails *)
   apply ev_0.
 Qed.

 Theorem ev100' : ev 100.
 Proof.
   repeat (apply ev_0). (* doesn't fail, applies ev_0 zero times *)
   repeat (apply ev_SS). apply ev_0. (* we can continue the proof *)
 Qed.

 Theorem silly1 : forall ae, aeval ae = aeval ae.
 Proof. try reflexivity. (* this just does reflexivity *) Qed.

 Theorem silly2 : forall (P : Prop), P -> P.
 Proof.
   intros P HP.
   try reflexivity. (* just reflexivity would have failed *)
   apply HP. (* we can still finish the proof in some other way *)
 Qed.

Lemma foo : forall n, ble_nat 0 n = true.
Proof.
  intros.
  destruct n.
    (* Leaves two subgoals, which are discharged identically...  *)
    Case "n=0". simpl. reflexivity.
    Case "n=Sn'". simpl. reflexivity.
Qed.

Lemma foo' : forall n, ble_nat 0 n = true.
Proof.
  intros.
  destruct n; (* [destruct] the current goal *)
  simpl; (* then [simpl] each resulting subgoal *)
  reflexivity. (* and do [reflexivity] on each resulting subgoal *)
Qed.

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  (* The remaining cases -- ANum and APlus -- are different *)
  Case "ANum". reflexivity.
  Case "APlus".
    destruct a1;
      (* Again, most cases follow directly by the IH *)
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    (* The interesting case, on which the [try...] does nothing,
       is when [e1 = ANum n]. In this case, we have to destruct
       [n] (to see whether the optimization applies) and rewrite
       with the induction hypothesis. *)
    SCase "a1 = ANum n". destruct n;
      simpl; rewrite IHa2; reflexivity.   Qed.

Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... or are immediate by definition *)
    try reflexivity.
  (* The interesting case is when a = APlus a1 a2. *)
  Case "APlus".
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    SCase "a1 = ANum n". destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].


Theorem optimize_0plus_sound''': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  aexp_cases (induction a) Case;
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    try reflexivity.
  (* At this point, there is already an ["APlus"] case name
     in the context.  The [Case "APlus"] here in the proof
     text has the effect of a sanity check: if the "Case"
     string in the context is anything _other_ than ["APlus"]
     (for example, because we added a clause to the definition
     of [aexp] and forgot to change the proof) we'll get a
     helpful error at this point telling us that this is now
     the wrong case. *)
  Case "APlus".
    aexp_cases (destruct a1) SCase;
      try (simpl; simpl in IHa1;
           rewrite IHa1; rewrite IHa2; reflexivity).
    SCase "ANum". destruct n;
      simpl; rewrite IHa2; reflexivity.  Qed.

(* Exercise: 3 stars (optimize_0plus_b) *)

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
    | BTrue => BTrue
    | BFalse => BFalse
    | BEq e1 e2 => BEq (optimize_0plus e1) (optimize_0plus e2)
    | BLe e1 e2 => BLe (optimize_0plus e1) (optimize_0plus e2)
    | BNot e1 => BNot (optimize_0plus_b e1)
    | BAnd e1 e2 => BAnd (optimize_0plus_b e1) (optimize_0plus_b e2)
  end.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros.
  induction b; simpl;
    try (repeat (rewrite optimize_0plus_sound));
    try (reflexivity).
  Case "BNot". rewrite IHb; reflexivity.
  Case "BAnd". rewrite IHb1; rewrite IHb2; reflexivity.
Qed.

Require Coq.omega.Omega.
Ltac omega := Coq.omega.Omega.omega.

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega.
Qed.

(* Evaluation as a Relation *)

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum  : forall (n: nat),
      aevalR (ANum n) n
  | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus: forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

Notation "e '||' n" := (aevalR e n) : type_scope.

End aevalR_first_try.

Reserved Notation "e '||' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) || n
  | E_APlus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 || n1) -> (e2 || n2) -> (APlus e1 e2) || (n1 + n2)
  | E_AMinus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 || n1) -> (e2 || n2) -> (AMinus e1 e2) || (n1 - n2)
  | E_AMult :  forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 || n1) -> (e2 || n2) -> (AMult e1 e2) || (n1 * n2)

  where "e '||' n" := (aevalR e n) : type_scope.

Tactic Notation "aevalR_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_ANum" | Case_aux c "E_APlus"
  | Case_aux c "E_AMinus" | Case_aux c "E_AMult" ].

Theorem aeval_iff_aevalR : forall a n,
  (a || n) <-> aeval a = n.
Proof.
 split.
 Case "->".
   intros H.
   aevalR_cases (induction H) SCase; simpl.
   SCase "E_ANum".
     reflexivity.
   SCase "E_APlus".
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   SCase "E_AMinus".
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   SCase "E_AMult".
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
 Case "<-".
   generalize dependent n.
   aexp_cases (induction a) SCase;
      simpl; intros; subst.
   SCase "ANum".
     apply E_ANum.
   SCase "APlus".
     apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   SCase "AMinus".
     apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   SCase "AMult".
     apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
Qed.

Theorem aeval_iff_aevalR' : forall a n,
  (a || n) <-> aeval a = n.
Proof.
  split.
  Case "->".
    intros H; induction H; subst; reflexivity.
  Case "<-".
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

(* Exercise: 3 stars (bevalR) *)

Inductive bevalR : bexp -> bool -> Prop :=
  | E_BTrue : bevalR BTrue true
  | E_BFalse : bevalR BFalse false
  | E_BEq :forall(a1 a2: aexp) (n1 n2: nat), (a1 || n1) -> (a2 || n2) -> bevalR (BEq a1 a2) (beq_nat n1 n2)
  | E_BLe :forall(a1 a2: aexp) (n1 n2: nat), (a1 || n1) -> (a2 || n2) -> bevalR (BLe a1 a2) (ble_nat n1 n2)
  | E_BNot :forall(b:bexp) (n1:bool), (bevalR b n1) -> bevalR (BNot b) (negb n1)
  | E_BAnd: forall (b1 b2:bexp) (n1 n2:bool), (bevalR b1 n1) -> (bevalR b2 n2) -> bevalR (BAnd b1 b2) (andb n1 n2).

Theorem beval_iff_bevalR : forall e b,
  (bevalR e b) <-> beval e = b.
Proof.
  split.
  Case "->".
  intros; induction H; simpl;
  try (apply aeval_iff_aevalR in H);
  try (apply aeval_iff_aevalR in H0); subst; reflexivity.
  Case "<-".
  generalize dependent b.
  induction e; simpl; intros; subst; constructor;
  try (apply aeval_iff_aevalR); try (apply IHe); try (apply IHe1);
  try (apply IHe2); reflexivity.
Qed.

Theorem eval_iff_bevalR: forall b n,
    (bevalR b n) <-> beval b = n.
Proof.
  split.
  Case "->".
    intros.
    induction H; simpl;
    try(apply aeval_iff_aevalR in H; apply aeval_iff_aevalR in H0);
    try(subst; reflexivity).
  Case "<-".
    generalize dependent n.
    induction b; simpl; intros; subst; constructor;
    try(apply aeval_iff_aevalR); try(apply IHb);
    try(apply IHb1); try(apply IHb2); try(reflexivity).
Qed.

End AExp.

Module aevalR_division.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | ADiv : aexp -> aexp -> aexp.   (* <--- new *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) || n
  | E_APlus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (APlus a1 a2) || (n1 + n2)
  | E_AMinus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (AMinus a1 a2) || (n1 - n2)
  | E_AMult :  forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (AMult a1 a2) || (n1 * n2)
  | E_ADiv :  forall (a1 a2: aexp) (n1 n2 n3: nat),
      (a1 || n1) -> (a2 || n2) -> (mult n2 n3 = n1) -> (ADiv a1 a2) || n3

where "a '||' n" := (aevalR a n) : type_scope.

End aevalR_division.

Module aevalR_extended.

Inductive aexp : Type :=
  | AAny  : aexp                   (* <--- NEW *)
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any : forall (n:nat),
      AAny || n                 (* <--- new *)
  | E_ANum : forall (n:nat),
      (ANum n) || n
  | E_APlus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (APlus a1 a2) || (n1 + n2)
  | E_AMinus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (AMinus a1 a2) || (n1 - n2)
  | E_AMult :  forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (AMult a1 a2) || (n1 * n2)

where "a '||' n" := (aevalR a n) : type_scope.

End aevalR_extended.
