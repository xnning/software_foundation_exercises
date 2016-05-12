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

Module Id.

Inductive id : Type :=
  Id : nat -> id.

Theorem eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
   intros id1 id2.
   destruct id1 as [n1]. destruct id2 as [n2].
   destruct (eq_nat_dec n1 n2) as [Heq | Hneq].
   Case "n1 = n2".
     left. rewrite Heq. reflexivity.
   Case "n1 <> n2".
     right. intros contra. inversion contra. apply Hneq. apply H0.
Defined.

Lemma eq_id : forall (T:Type) x (p q:T),
              (if eq_id_dec x x then p else q) = p.
Proof.
  intros.
  destruct (eq_id_dec x x).
  Case "x = x".
    reflexivity.
  Case "x <> x (impossible)".
    apply ex_falso_quodlibet; apply n; reflexivity. Qed.

(* Exercise: 1 star, optional (neq_id) *)

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y ->
               (if eq_id_dec x y then p else q) = q.
Proof.
  intros.
  destruct (eq_id_dec x y).
  Case "x = y". apply ex_falso_quodlibet; apply H; apply e.
  Case "x <> y". reflexivity.
Qed.

End Id.

Definition state := id -> nat.

Definition empty_state : state :=
  fun _ => 0.

Definition update (st : state) (x : id) (n : nat) : state :=
  fun x' => if eq_id_dec x x' then n else st x'.

(* Exercise: 1 star (update_eq) *)

Theorem update_eq : forall n x st,
  (update st x n) x = n.
Proof.
  intros. unfold update. apply eq_id.
Qed.

(* Exercise: 1 star (update_neq) *)

Theorem update_neq : forall x2 x1 n st,
  x2 <> x1 ->
  (update st x2 n) x1 = (st x1).
Proof.
  intros. unfold update. apply neq_id. apply H. Qed.

(* Exercise: 1 star (update_example) *)

Theorem update_example : forall (n:nat),
  (update empty_state (Id 2) n) (Id 3) = 0.
Proof.
  intros. unfold update.
  apply neq_id. intros contra. inversion contra.
Qed.

(* Exercise: 1 star (update_shadow) *)

Theorem update_shadow : forall n1 n2 x1 x2 (st : state),
   (update  (update st x2 n1) x2 n2) x1 = (update st x2 n2) x1.
Proof.
  intros.
  unfold update. destruct (eq_id_dec x2 x1); reflexivity.
Qed.

(* Exercise: 2 stars (update_same) *)

Theorem update_same : forall n1 x1 x2 (st : state),
  st x1 = n1 ->
  (update st x1 n1) x2 = st x2.
Proof.
  intros. unfold update. destruct (eq_id_dec x1 x2). subst. reflexivity.
  reflexivity.
Qed.

(* Exercise: 3 stars (update_permute) *)
Theorem update_permute : forall n1 n2 x1 x2 x3 st,
  x2 <> x1 ->
  (update (update st x2 n1) x1 n2) x3 = (update (update st x1 n2) x2 n1) x3.
Proof.
  intros. unfold update.
  destruct (eq_id_dec x1 x3) eqn: x1x3.
    destruct (eq_id_dec x2 x3) eqn: x2x3.
      apply ex_falso_quodlibet. apply H. subst. reflexivity.
      reflexivity.
    destruct (eq_id_dec x2 x3) eqn: x2x3; reflexivity.
Qed.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp                (* <----- NEW *)
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "AId" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BTrue" | Case_aux c "BFalse" | Case_aux c "BEq"
  | Case_aux c "BLe" | Case_aux c "BNot" | Case_aux c "BAnd" ].

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                        (* <----- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => ble_nat (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Example aexp1 :
  aeval (update empty_state X 5)
        (APlus (ANum 3) (AMult (AId X) (ANum 2)))
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
  beval (update empty_state X 5)
        (BAnd BTrue (BNot (BLe (AId X) (ANum 4))))
  = true.
Proof. reflexivity. Qed.

(* Commands *)

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";;"
  | Case_aux c "IFB" | Case_aux c "WHILE" ].

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

Definition fact_in_coq : com :=
  Z ::= AId X;;
  Y ::= ANum 1;;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);;
    Z ::= AMinus (AId Z) (ANum 1)
  END.

Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;;
  X ::= AMinus (AId X) (ANum 1).

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= ANum 3 ;;
  Z ::= ANum 5 ;;
  subtract_slowly.

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

(* Evaluation *)

Fixpoint ceval_fun_no_while (st : state) (c : com) : state :=
  match c with
    | SKIP =>
        st
    | x ::= a1 =>
        update st x (aeval st a1)
    | c1 ;; c2 =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | WHILE b DO c END =>
        st  (* bogus *)
  end.

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st || st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st || (update st x n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  || st' ->
      c2 / st' || st'' ->
      (c1 ;; c2) / st || st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st || st
  | E_WhileLoop : forall st st' st'' b c,
      beval st b = true ->
      c / st || st' ->
      (WHILE b DO c END) / st' || st'' ->
      (WHILE b DO c END) / st || st''

  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" ].

Example ceval_example1:
    (X ::= ANum 2;;
     IFB BLe (AId X) (ANum 1)
       THEN Y ::= ANum 3
       ELSE Z ::= ANum 4
     FI)
   / empty_state
   || (update (update empty_state X 2) Z 4).
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with (update empty_state X 2).
  Case "assignment command".
    apply E_Ass. reflexivity.
  Case "if command".
    apply E_IfFalse.
      reflexivity.
      apply E_Ass. reflexivity.  Qed.

(* Exercise: 2 stars (ceval_example2) *)

Example ceval_example2:
    (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state ||
    (update (update (update empty_state X 0) Y 1) Z 2).
Proof.
  apply E_Seq with (update empty_state X 0).
  apply E_Ass. reflexivity.
  apply E_Seq with (update (update empty_state X 0) Y 1).
  apply E_Ass. reflexivity.
  apply E_Ass. reflexivity.
Qed.

(* Exercise: 3 stars, advanced (pup_to_n) *)

Definition pup_to_n : com :=
  Y ::= ANum 0;;
  WHILE (BLe (ANum 1) (AId X)) DO
    Y ::= APlus (AId Y) (AId X);;
    X ::= AMinus (AId X) (ANum 1)
  END.

Theorem pup_to_2_ceval :
  pup_to_n / (update empty_state X 2) ||
    update (update (update (update (update (update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0.
Proof.
  unfold pup_to_n.
  apply E_Seq with (st':= (update (update empty_state X 2) Y 0)).
    apply E_Ass. reflexivity.
    apply E_WhileLoop with (update (update (update (update empty_state X 2) Y 0) Y 2) X 1).
    reflexivity. apply E_Seq with (update (update (update empty_state X 2) Y 0) Y 2); try(apply E_Ass; reflexivity).
    apply E_WhileLoop with (update (update (update (update (update (update empty_state X 2) Y 0) Y 2) X 1) Y 3) X 0).
    reflexivity. apply E_Seq with (update (update (update (update (update empty_state X 2) Y 0) Y 2) X 1) Y 3); try(apply E_Ass; reflexivity).
    apply E_WhileEnd. reflexivity.
Qed.

Theorem ceval_deterministic: forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  ceval_cases (induction E1) Case;
           intros st2 E2; inversion E2; subst.
  Case "E_Skip". reflexivity.
  Case "E_Ass". reflexivity.
  Case "E_Seq".
    assert (st' = st'0) as EQ1.
      SCase "Proof of assertion". apply IHE1_1; assumption.
    subst st'0.
    apply IHE1_2. assumption.
  Case "E_IfTrue".
    SCase "b1 evaluates to true".
      apply IHE1. assumption.
    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H5. inversion H5.
  Case "E_IfFalse".
    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H5. inversion H5.
    SCase "b1 evaluates to false".
      apply IHE1. assumption.
  Case "E_WhileEnd".
    SCase "b1 evaluates to false".
      reflexivity.
    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H2. inversion H2.
  Case "E_WhileLoop".
    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H4. inversion H4.
    SCase "b1 evaluates to true".
      assert (st' = st'0) as EQ1.
        SSCase "Proof of assertion". apply IHE1_1; assumption.
      subst st'0.
      apply IHE1_2. assumption.  Qed.

(* Reasoning About Imp Programs *)

Theorem plus2_spec : forall st n st',
  st X = n ->
  plus2 / st || st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  (* Inverting Heval essentially forces Coq to expand one
     step of the ceval computation - in this case revealing
     that st' must be st extended with the new value of X,
     since plus2 is an assignment *)
  inversion Heval. subst. clear Heval. simpl.
  apply update_eq.  Qed.

(* Exercise: 3 stars (XtimesYinZ_spec) *)

Theorem XtimesYinZ_spec : forall st x y st',
    st X = x ->
    st Y = y ->
    XtimesYinZ / st || st' ->
    st' Z = x * y.
Proof.
  intros.
  inversion H1. subst. simpl. apply update_eq. Qed.

(* Exercise: 3 stars (loop_never_stops) *)

Theorem loop_never_stops : forall st st',
  ~(loop / st || st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef eqn:Heqloopdef.
    (* Proceed by induction on the assumed derivation showing that
     [loopdef] terminates.  Most of the cases are immediately
     contradictory (and so can be solved in one step with
     [inversion]). *)
  induction contra; try(inversion Heqloopdef).
  subst. inversion H.
  subst. apply IHcontra2. reflexivity.
Qed.

(* Exercise: 3 stars (no_whilesR) *)

Fixpoint no_whiles (c : com) : bool := match c with
  | SKIP       => true
  | _ ::= _    => true
  | c1 ;; c2  => andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI => andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END  => false
  end.

Inductive no_whilesR: com -> Prop :=
  | NWSkip : no_whilesR SKIP
  | NWAss : forall x e, no_whilesR (x ::= e)
  | NWSeq : forall e1 e2, no_whilesR e1 -> no_whilesR e2 -> no_whilesR (e1 ;; e2)
  | NWIf : forall b e1 e2, no_whilesR e1 -> no_whilesR e2 -> no_whilesR (IFB b THEN e1 ELSE e2 FI)
  .

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  split.
  Case "->".
    intros. induction c; try(constructor);
    try(inversion H; apply IHc1; apply andb_true_elim1 in H1; assumption);
    try(inversion H; apply IHc2; apply andb_true_elim2 in H1; assumption).
  Case "<-".
    intros. induction H; try(reflexivity);
    try(simpl; rewrite IHno_whilesR1; rewrite IHno_whilesR2; reflexivity).
Qed.
