Require Export Imp.

(* a toy language *)

Inductive tm : Type :=
  | C : nat -> tm         (* Constant *)
  | P : tm -> tm -> tm.   (* Plus *)

Tactic Notation "tm_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "C" | Case_aux c "P" ].

Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P a1 a2 => evalF a1 + evalF a2
  end.

Reserved Notation " t '||' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      C n || n
  | E_Plus : forall t1 t2 n1 n2,
      t1 || n1 ->
      t2 || n2 ->
      P t1 t2 || (n1 + n2)

  where " t '||' n " := (eval t n).

Tactic Notation "eval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Const" | Case_aux c "E_Plus" ].

Module SimpleArith1.

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) ==> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 ==> t1' ->
      P t1 t2 ==> P t1' t2
  | ST_Plus2 : forall n1 t2 t2',
      t2 ==> t2' ->
      P (C n1) t2 ==> P (C n1) t2'

  where " t '==>' t' " := (step t t').

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_PlusConstConst"
  | Case_aux c "ST_Plus1" | Case_aux c "ST_Plus2" ].

Example test_step_1 :
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
      ==>
      P
        (C (0 + 3))
        (P (C 2) (C 4)).
Proof.
  apply ST_Plus1. apply ST_PlusConstConst.  Qed.

(* Exercise: 1 star (test_step_2) *)

Example test_step_2 :
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
      ==>
      P
        (C 0)
        (P
          (C 2)
          (C (0 + 3))).
Proof.
  repeat (apply ST_Plus2).
  apply ST_PlusConstConst.
Qed.

(* Relations *)

Definition relation (X: Type) := X->X->Prop.

Definition deterministic {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Theorem step_deterministic:
  deterministic step.
Proof.
  unfold deterministic. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  step_cases (induction Hy1) Case; intros y2 Hy2.
    Case "ST_PlusConstConst". step_cases (inversion Hy2) SCase.
      SCase "ST_PlusConstConst". reflexivity.
      SCase "ST_Plus1". inversion H2.
      SCase "ST_Plus2". inversion H2.
    Case "ST_Plus1". step_cases (inversion Hy2) SCase.
      SCase "ST_PlusConstConst". rewrite <- H0 in Hy1. inversion Hy1.
      SCase "ST_Plus1".
        rewrite <- (IHHy1 t1'0).
        reflexivity. assumption.
      SCase "ST_Plus2". rewrite <- H in Hy1. inversion Hy1.
    Case "ST_Plus2". step_cases (inversion Hy2) SCase.
      SCase "ST_PlusConstConst". rewrite <- H1 in Hy1. inversion Hy1.
      SCase "ST_Plus1". inversion H2.
      SCase "ST_Plus2".
        rewrite <- (IHHy1 t2'0).
        reflexivity. assumption.
Qed.

Theorem step_deterministic_alt: deterministic step.
Proof.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  step_cases (induction Hy1) Case; intros y2 Hy2;
    inversion Hy2; subst; try (solve by inversion).
  Case "ST_PlusConstConst". reflexivity.
  Case "ST_Plus1".
    apply IHHy1 in H2. rewrite H2. reflexivity.
  Case "ST_Plus2".
    apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.


End SimpleArith1.

Inductive value : tm -> Prop :=
  v_const : forall n, value (C n).

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
          P (C n1) (C n2)
      ==> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 ==> t1' ->
        P t1 t2 ==> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 ->                     (* <----- n.b. *)
        t2 ==> t2' ->
        P v1 t2 ==> P v1 t2'

  where " t '==>' t' " := (step t t').

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_PlusConstConst"
  | Case_aux c "ST_Plus1" | Case_aux c "ST_Plus2" ].

(* Exercise: 3 stars (redo_determinism) *)

Theorem step_deterministic :
  deterministic step.
Proof.
  unfold deterministic. intros x y1 y2 H1 H2.
  generalize dependent y2.
  step_cases (induction H1) Case; intros y2 H2; step_cases (inversion H2) SCase; subst; try(solve by inversion).
  Case "ST_PlusConstConst".
    reflexivity.
  Case "ST_Plus1".
    rewrite (IHstep t1'0). reflexivity. assumption.
    inversion H3. subst. inversion H1.
  Case "ST_Plus2".
    inversion H. subst. inversion H5.
    rewrite (IHstep t2'0). reflexivity. assumption.
Qed.

(* Strong Progress and Normal Forms *)

Theorem strong_progress : forall t,
  value t \/ (exists t', t ==> t').
Proof.
  tm_cases (induction t) Case.
    Case "C". left. apply v_const.
    Case "P". right. inversion IHt1.
      SCase "l". inversion IHt2.
        SSCase "l". inversion H. inversion H0.
          exists (C (n + n0)).
          apply ST_PlusConstConst.
        SSCase "r". inversion H0 as [t' H1].
          exists (P t1 t').
          apply ST_Plus2. apply H. apply H1.
      SCase "r". inversion H as [t' H0].
          exists (P t' t2).
          apply ST_Plus1. apply H0.  Qed.

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.

Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Proof.
  unfold normal_form. intros v H. inversion H.
  intros contra. inversion contra. inversion H1.
Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof. (* a corollary of [strong_progress]... *)
  unfold normal_form. intros t H.
  assert (G : value t \/ exists t', t ==> t').
    SCase "Proof of assertion". apply strong_progress.
  inversion G.
    SCase "l". apply H0.
    SCase "r". apply ex_falso_quodlibet. apply H. assumption.  Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  split. apply nf_is_value. apply value_is_nf. Qed.

Module Temp1.

Inductive value : tm -> Prop :=
| v_const : forall n, value (C n)
| v_funny : forall t1 n2,                       (* <---- *)
              value (P t1 (C n2)).

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) ==> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 ==> t1' ->
      P t1 t2 ==> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 ==> t2' ->
      P v1 t2 ==> P v1 t2'

  where " t '==>' t' " := (step t t').

(* Exercise: 3 stars, advanced (value_not_same_as_normal_form) *)

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
  exists (P (C 1) (C 2)). split.
  constructor.
  unfold normal_form. unfold not. intros. apply H. exists (C (1 + 2)). constructor.
Qed.

End Temp1.

Module Temp2.

Inductive value : tm -> Prop :=
| v_const : forall n, value (C n).

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_Funny : forall n,                         (* <---- *)
      C n ==> P (C n) (C 0)
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) ==> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 ==> t1' ->
      P t1 t2 ==> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      value v1 ->
      t2 ==> t2' ->
      P v1 t2 ==> P v1 t2'

  where " t '==>' t' " := (step t t').

(* Exercise: 2 stars, advanced (value_not_same_as_normal_form) *)

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
  exists (C 1).
  split. constructor.
  unfold normal_form. unfold not. intros. apply H. exists (P (C 1) (C 0)). constructor.
Qed.

End Temp2.

Module Temp3.

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
      P (C n1) (C n2) ==> C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 ==> t1' ->
      P t1 t2 ==> P t1' t2

  where " t '==>' t' " := (step t t').

(** **** Exercise: 3 stars, advanced (value_not_same_as_normal_form')  *)

Lemma value_not_same_as_normal_form :
  exists t, ~ value t /\ normal_form step t.
Proof.
  exists (P (C 1) (P (C 2) (C 3))).
  split. unfold not. intros. inversion H.
  unfold normal_form. unfold not. intros. solve by inversion 3.
Qed.

End Temp3.

(* Additional Exercises *)

Module Temp4.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
  | v_true : value ttrue
  | v_false : value tfalse.

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      tif ttrue t1 t2 ==> t1
  | ST_IfFalse : forall t1 t2,
      tif tfalse t1 t2 ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      tif t1 t2 t3 ==> tif t1' t2 t3

  where " t '==>' t' " := (step t t').

(* Exercise: 3 stars, optional (progress_bool) *)

Theorem strong_progress : forall t,
  value t \/ (exists t', t ==> t').
Proof.
  intros.
  induction t; try(left; constructor).
  right. inversion IHt1.
  inversion H. exists t2. constructor. exists t3. constructor.
  inversion H. exists (tif x t2 t3). constructor. apply H0.
Qed.

(* Exercise: 2 stars, optional (step_deterministic) *)

Theorem step_deterministic :
  deterministic step.
Proof.
  unfold deterministic. intros.
  generalize dependent y2.
  induction H; intros; inversion H0; subst; try(reflexivity); try(solve by inversion).
  rewrite (IHstep t1'0). reflexivity. apply H5.
Qed.

Module Temp5.

(* Exercise: 2 stars (smallstep_bool_shortcut) *)

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      tif ttrue t1 t2 ==> t1
  | ST_IfFalse : forall t1 t2,
      tif tfalse t1 t2 ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      tif t1 t2 t3 ==> tif t1' t2 t3
  | ST_ShortCircuit : forall t1 t2,
      tif t1 t2 t2 ==> t2

  where " t '==>' t' " := (step t t').

Definition bool_step_prop4 :=
         tif
            (tif ttrue ttrue ttrue)
            tfalse
            tfalse
     ==>
         tfalse.

Example bool_step_prop4_holds :
  bool_step_prop4.
Proof.
  unfold bool_step_prop4.
  constructor.
Qed.

End Temp5.
End Temp4.