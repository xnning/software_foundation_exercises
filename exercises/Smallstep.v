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

(* Multi-Step Reduction *)

Inductive multi {X:Type} (R: relation X) : relation X :=
  | multi_refl  : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Tactic Notation "multi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "multi_refl" | Case_aux c "multi_step" ].

Notation " t '==>*' t' " := (multi step t t') (at level 40).

Theorem multi_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y. apply H. apply multi_refl.   Qed.

Theorem multi_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  multi_cases (induction G) Case.
    Case "multi_refl". assumption.
    Case "multi_step".
      apply multi_step with y. assumption.
      apply IHG. assumption.  Qed.

(* Examples *)

Lemma test_multistep_1:
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
   ==>*
      C ((0 + 3) + (2 + 4)).
Proof.
  apply multi_step with
            (P
                (C (0 + 3))
                (P (C 2) (C 4))).
  apply ST_Plus1. apply ST_PlusConstConst.
  apply multi_step with
            (P
                (C (0 + 3))
                (C (2 + 4))).
  apply ST_Plus2. apply v_const.
  apply ST_PlusConstConst.
  apply multi_R.
  apply ST_PlusConstConst. Qed.

(** **** Exercise: 1 star, optional (test_multistep_2)  *)
Lemma test_multistep_2:
  C 3 ==>* C 3.
Proof.
  constructor. Qed.

(** **** Exercise: 1 star, optional (test_multistep_3)  *)
Lemma test_multistep_3:
      P (C 0) (C 3)
   ==>*
      P (C 0) (C 3).
Proof.
  constructor. Qed.

(** **** Exercise: 2 stars (test_multistep_4)  *)
Lemma test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  ==>*
      P
        (C 0)
        (C (2 + (0 + 3))).
Proof.
  apply multi_step with (P (C 0) (P (C 2) (C (0 + 3)))).
  repeat (apply ST_Plus2). constructor. constructor.
  apply ST_PlusConstConst.
  apply multi_step with (P (C 0) (C (2 + (0 + 3)))).
  apply ST_Plus2. constructor. apply ST_PlusConstConst.
  constructor.
Qed.

(* Normal Forms Again *)

Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) :=
  (t ==>* t' /\ step_normal_form t').

(** **** Exercise: 3 stars, optional (normal_forms_unique)  *)
Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
  unfold deterministic. unfold normal_form_of.  intros x y1 y2 P1 P2.
  inversion P1 as [P11 P12]; clear P1. inversion P2 as [P21 P22]; clear P2.
  generalize dependent y2.
  multi_cases (induction P11) Case; intros.
  Case "multi_refl".
    multi_cases (inversion P21) SCase.
    reflexivity.
    apply ex_falso_quodlibet. apply P12. exists y. assumption.
  Case "multi_step".
    multi_cases (inversion P21) SCase; subst.
    apply ex_falso_quodlibet. apply P22. exists y. apply H.
    apply IHP11. apply P12.
      assert (y0 = y). apply (step_deterministic x y0 y); assumption.
      subst. assumption. assumption.
Qed.

Definition normalizing {X:Type} (R:relation X) :=
  forall t, exists t',
    (multi R) t t' /\ normal_form R t'.

Lemma multistep_congr_1 : forall t1 t1' t2,
     t1 ==>* t1' ->
     P t1 t2 ==>* P t1' t2.
Proof.
  intros t1 t1' t2 H. multi_cases (induction H) Case.
    Case "multi_refl". apply multi_refl.
    Case "multi_step". apply multi_step with (P y t2).
        apply ST_Plus1. apply H.
        apply IHmulti.  Qed.

(** **** Exercise: 2 stars (multistep_congr_2)  *)
Lemma multistep_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 ==>* t2' ->
     P t1 t2 ==>* P t1 t2'.
Proof.
  intros. multi_cases (induction H0) Case.
  Case "multi_refl". constructor.
  Case "multi_step". apply multi_step with (P t1 y).
    apply ST_Plus2; assumption.
    assumption.
Qed.

Theorem step_normalizing :
  normalizing step.
Proof.
  unfold normalizing.
  tm_cases (induction t) Case.
    Case "C".
      exists (C n).
      split.
      SCase "l". apply multi_refl.
      SCase "r".
        (* We can use [rewrite] with "iff" statements, not
           just equalities: *)
        rewrite nf_same_as_value. apply v_const.
    Case "P".
      inversion IHt1 as [t1' H1]; clear IHt1. inversion IHt2 as [t2' H2]; clear IHt2.
      inversion H1 as [H11 H12]; clear H1. inversion H2 as [H21 H22]; clear H2.
      rewrite nf_same_as_value in H12. rewrite nf_same_as_value in H22.
      inversion H12 as [n1]. inversion H22 as [n2].
      rewrite <- H in H11.
      rewrite <- H0 in H21.
      exists (C (n1 + n2)).
      split.
        SCase "l".
          apply multi_trans with (P (C n1) t2).
          apply multistep_congr_1. apply H11.
          apply multi_trans with
             (P (C n1) (C n2)).
          apply multistep_congr_2. apply v_const. apply H21.
          apply multi_R. apply ST_PlusConstConst.
        SCase "r".
          rewrite nf_same_as_value. apply v_const.  Qed.

(* Equivalence of Big-Step and Small-Step Reduction *)

(** **** Exercise: 3 stars (eval__multistep)  *)

Theorem eval__multistep : forall t n,
  t || n -> t ==>* C n.
Proof.
  intros.
  eval_cases (induction H) Case.
  Case "E_Const". constructor.
  Case "E_Plus". apply multi_trans with (P (C n1) (C n2)).
    apply multi_trans with (P (C n1) t2).
    apply multistep_congr_1. assumption.
    apply multistep_congr_2. apply nf_same_as_value. apply value_is_nf. constructor. assumption.
    apply multi_step with (C (n1 + n2)).
    apply ST_PlusConstConst. constructor.
Qed.

(** **** Exercise: 3 stars (step__eval)  *)
Lemma step__eval : forall t t' n,
     t ==> t' ->
     t' || n ->
     t || n.
Proof.
  intros t t' n Hs. generalize dependent n.
  step_cases (induction Hs) Case; intros.
  Case "ST_PlusConstConst".
    inversion H. apply E_Plus; constructor.
  Case "ST_Plus1".
    inversion H. apply E_Plus. apply IHHs. assumption. assumption.
  Case "ST_Plus2".
    inversion H0. apply E_Plus. assumption. apply IHHs. assumption.
Qed.


(* Exercise: 3 stars (multistep__eval) *)

Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t || n.
Proof.
  unfold normal_form_of. unfold step_normal_form.
  intros. destruct H as [H1 H2]. apply nf_same_as_value in H2. inversion H2.
  exists n. split. reflexivity.
  multi_cases (induction H1) Case; subst.
  Case "multi_refl". constructor.
  Case "multi_step". apply step__eval with y. assumption.
   apply IHmulti. constructor. reflexivity.
Qed.

(* Additional Exercises *)

(* Exercise: 3 stars, optional (interp_tm) *)

Theorem evalF_eval : forall t n,
  evalF t = n <-> t || n.
Proof.
  split.
  Case "->". generalize dependent n. tm_cases (induction t) SCase; intros.
    SCase "C". simpl in H. subst. constructor.
    SCase "P". simpl in H. subst. apply E_Plus.
      apply IHt1. reflexivity.
      apply IHt2. reflexivity.
  Case "<-". intros.
    eval_cases (induction H) SCase; subst; reflexivity.
Qed.

(* Exercise: 4 stars (combined_properties) *)


Module Combined.

Inductive tm : Type :=
  | C : nat -> tm
  | P : tm -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm.

Tactic Notation "tm_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "C" | Case_aux c "P"
  | Case_aux c "ttrue" | Case_aux c "tfalse" | Case_aux c "tif" ].

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n)
  | v_true : value ttrue
  | v_false : value tfalse.

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
  | ST_IfTrue : forall t1 t2,
      tif ttrue t1 t2 ==> t1
  | ST_IfFalse : forall t1 t2,
      tif tfalse t1 t2 ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      tif t1 t2 t3 ==> tif t1' t2 t3

  where " t '==>' t' " := (step t t').

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_PlusConstConst"
  | Case_aux c "ST_Plus1" | Case_aux c "ST_Plus2"
  | Case_aux c "ST_IfTrue" | Case_aux c "ST_IfFalse" | Case_aux c "ST_If" ].

Theorem step_deterministic:
  deterministic step.
Proof.
  unfold deterministic. intros x y1 y2 H1 H2.
  generalize dependent y2.
  step_cases (induction H1) Case; intros; inversion H2; subst; try(solve by inversion 2); try(reflexivity).
  Case "ST_Plus1". apply IHstep in H4. subst. reflexivity.
  Case "ST_Plus2". apply IHstep in H6. subst. reflexivity.
  Case "ST_If". apply IHstep in H5. subst. reflexivity.
Qed.

Theorem strong_progress : exists t,
  ~ (value t \/ (exists t', t ==> t')).
Proof.
  unfold not.
  exists (tif (C 0) (C 0) (C 0)).
  intros. destruct H as [H1 | H2]; try (solve by inversion 3).
Qed.

End Combined.

(* Small-Step Imp *)

Inductive aval : aexp -> Prop :=
  av_num : forall n, aval (ANum n).

Reserved Notation " t '/' st '==>a' t' " (at level 40, st at level 39).

Inductive astep : state -> aexp -> aexp -> Prop :=
  | AS_Id : forall st i,
      AId i / st ==>a ANum (st i)
  | AS_Plus : forall st n1 n2,
      APlus (ANum n1) (ANum n2) / st ==>a ANum (n1 + n2)
  | AS_Plus1 : forall st a1 a1' a2,
      a1 / st ==>a a1' ->
      (APlus a1 a2) / st ==>a (APlus a1' a2)
  | AS_Plus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st ==>a a2' ->
      (APlus v1 a2) / st ==>a (APlus v1 a2')
  | AS_Minus : forall st n1 n2,
      (AMinus (ANum n1) (ANum n2)) / st ==>a (ANum (minus n1 n2))
  | AS_Minus1 : forall st a1 a1' a2,
      a1 / st ==>a a1' ->
      (AMinus a1 a2) / st ==>a (AMinus a1' a2)
  | AS_Minus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st ==>a a2' ->
      (AMinus v1 a2) / st ==>a (AMinus v1 a2')
  | AS_Mult : forall st n1 n2,
      (AMult (ANum n1) (ANum n2)) / st ==>a (ANum (mult n1 n2))
  | AS_Mult1 : forall st a1 a1' a2,
      a1 / st ==>a a1' ->
      (AMult (a1) (a2)) / st ==>a (AMult (a1') (a2))
  | AS_Mult2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st ==>a a2' ->
      (AMult v1 a2) / st ==>a (AMult v1 a2')

    where " t '/' st '==>a' t' " := (astep st t t').

Reserved Notation " t '/' st '==>b' t' " (at level 40, st at level 39).

Inductive bstep : state -> bexp -> bexp -> Prop :=
  | BS_Eq : forall st n1 n2,
      (BEq (ANum n1) (ANum n2)) / st ==>b
      (if (beq_nat n1 n2) then BTrue else BFalse)
  | BS_Eq1 : forall st a1 a1' a2,
      a1 / st ==>a a1' ->
      (BEq a1 a2) / st ==>b (BEq a1' a2)
  | BS_Eq2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st ==>a a2' ->
      (BEq v1 a2) / st ==>b (BEq v1 a2')
  | BS_LtEq : forall st n1 n2,
      (BLe (ANum n1) (ANum n2)) / st ==>b
               (if (ble_nat n1 n2) then BTrue else BFalse)
  | BS_LtEq1 : forall st a1 a1' a2,
      a1 / st ==>a a1' ->
      (BLe a1 a2) / st ==>b (BLe a1' a2)
  | BS_LtEq2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st ==>a a2' ->
      (BLe v1 a2) / st ==>b (BLe v1 (a2'))
  | BS_NotTrue : forall st,
      (BNot BTrue) / st ==>b BFalse
  | BS_NotFalse : forall st,
      (BNot BFalse) / st ==>b BTrue
  | BS_NotStep : forall st b1 b1',
      b1 / st ==>b b1' ->
      (BNot b1) / st ==>b (BNot b1')
  | BS_AndTrueTrue : forall st,
      (BAnd BTrue BTrue) / st ==>b BTrue
  | BS_AndTrueFalse : forall st,
      (BAnd BTrue BFalse) / st ==>b BFalse
  | BS_AndFalse : forall st b2,
      (BAnd BFalse b2) / st ==>b BFalse
  | BS_AndTrueStep : forall st b2 b2',
      b2 / st ==>b b2' ->
      (BAnd BTrue b2) / st ==>b (BAnd BTrue b2')
  | BS_AndStep : forall st b1 b1' b2,
      b1 / st ==>b b1' ->
      (BAnd b1 b2) / st ==>b (BAnd b1' b2)

  where " t '/' st '==>b' t' " := (bstep st t t').

Reserved Notation " t '/' st '==>' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st i a a',
      a / st ==>a a' ->
      (i ::= a) / st ==> (i ::= a') / st
  | CS_Ass : forall st i n,
      (i ::= (ANum n)) / st ==> SKIP / (update st i n)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st ==> c1' / st' ->
      (c1 ;; c2) / st ==> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st ==> c2 / st
  | CS_IfTrue : forall st c1 c2,
      IFB BTrue THEN c1 ELSE c2 FI / st ==> c1 / st
  | CS_IfFalse : forall st c1 c2,
      IFB BFalse THEN c1 ELSE c2 FI / st ==> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b / st ==>b b' ->
      IFB b THEN c1 ELSE c2 FI / st ==> (IFB b' THEN c1 ELSE c2 FI) / st
  | CS_While : forall st b c1,
          (WHILE b DO c1 END) / st
      ==> (IFB b THEN (c1;; (WHILE b DO c1 END)) ELSE SKIP FI) / st

  where " t '/' st '==>' t' '/' st' " := (cstep (t,st) (t',st')).

Module CImp.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  (* New: *)
  | CPar : com -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "PAR" ].

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' b 'THEN' c1 'ELSE' c2 'FI'" :=
  (CIf b c1 c2) (at level 80, right associativity).
Notation "'PAR' c1 'WITH' c2 'END'" :=
  (CPar c1 c2) (at level 80, right associativity).

Inductive cstep : (com * state)  -> (com * state) -> Prop :=
    (* Old part *)
  | CS_AssStep : forall st i a a',
      a / st ==>a a' ->
      (i ::= a) / st ==> (i ::= a') / st
  | CS_Ass : forall st i n,
      (i ::= (ANum n)) / st ==> SKIP / (update st i n)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st ==> c1' / st' ->
      (c1 ;; c2) / st ==> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st ==> c2 / st
  | CS_IfTrue : forall st c1 c2,
      (IFB BTrue THEN c1 ELSE c2 FI) / st ==> c1 / st
  | CS_IfFalse : forall st c1 c2,
      (IFB BFalse THEN c1 ELSE c2 FI) / st ==> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b /st ==>b b' ->
      (IFB b THEN c1 ELSE c2 FI) / st ==> (IFB b' THEN c1 ELSE c2 FI) / st
  | CS_While : forall st b c1,
      (WHILE b DO c1 END) / st ==>
               (IFB b THEN (c1;; (WHILE b DO c1 END)) ELSE SKIP FI) / st
    (* New part: *)
  | CS_Par1 : forall st c1 c1' c2 st',
      c1 / st ==> c1' / st' ->
      (PAR c1 WITH c2 END) / st ==> (PAR c1' WITH c2 END) / st'
  | CS_Par2 : forall st c1 c2 c2' st',
      c2 / st ==> c2' / st' ->
      (PAR c1 WITH c2 END) / st ==> (PAR c1 WITH c2' END) / st'
  | CS_ParDone : forall st,
      (PAR SKIP WITH SKIP END) / st ==> SKIP / st
  where " t '/' st '==>' t' '/' st' " := (cstep (t,st) (t',st')).


Definition cmultistep := multi cstep.

Notation " t '/' st '==>*' t' '/' st' " :=
   (multi cstep  (t,st) (t',st'))
   (at level 40, st at level 39, t' at level 39).

Definition par_loop : com :=
  PAR
    Y ::= ANum 1
  WITH
    WHILE BEq (AId Y) (ANum 0) DO
      X ::= APlus (AId X) (ANum 1)
    END
  END.

Example par_loop_example_0:
  exists st',
       par_loop / empty_state  ==>* SKIP / st'
    /\ st' X = 0.
Proof.
  eapply ex_intro. split.
  unfold par_loop.
  eapply multi_step. apply CS_Par1.
    apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  eapply multi_refl.
  reflexivity. Qed.

Example par_loop_example_2:
  exists st',
       par_loop / empty_state ==>* SKIP / st'
    /\ st' X = 2.
Proof.
  eapply ex_intro. split.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.

  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.

  eapply multi_step. apply CS_Par1. apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  eapply multi_refl.
  reflexivity. Qed.

Require Coq.omega.Omega.
Ltac omega := Coq.omega.Omega.omega.

(** **** Exercise: 3 stars, optional  *)
Lemma par_body_n__Sn : forall n st,
  st X = n /\ st Y = 0 ->
  par_loop / st ==>* par_loop / (update st X (S n)).
Proof.
  intros. unfold par_loop. destruct H as [H1 H2].
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep. apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep. rewrite H2. apply BS_Eq.
  eapply multi_step. apply CS_Par2. simpl. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep. apply CS_AssStep. apply AS_Plus1. apply AS_Id. rewrite H1.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep. apply CS_AssStep. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep. apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.
  assert (n + 1 = S n). omega. rewrite H.
  eapply multi_refl.
Qed.

(* Exercise: 3 stars, optional *)

Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
  intros. unfold par_loop.
  induction n as [| n'].
  exists st. split. apply multi_refl. assumption.
  inversion IHn'. clear IHn'.
  destruct H0 as [ H1 [H2 H3]].
  exists (update x X (S n')). split.
  eapply multi_trans. apply H1.
  apply par_body_n__Sn. split; assumption.
  split. reflexivity. unfold update. simpl. assumption.
Qed.

Theorem par_loop_any_X:
  forall n, exists st',
    par_loop / empty_state ==>*  SKIP / st'
    /\ st' X = n.
Proof.
  intros n.
  destruct (par_body_n n empty_state).
    split; unfold update; reflexivity.

  rename x into st.
  inversion H as [H' [HX HY]]; clear H.
  exists (update st Y 1). split.
  eapply multi_trans with (par_loop,st). apply H'.
  eapply multi_step. apply CS_Par1. apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id. rewrite update_eq.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  apply multi_refl.

  rewrite update_neq. assumption. intro X; inversion X.
Qed.

End CImp.