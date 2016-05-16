Require Export Smallstep.

Hint Constructors multi.

(* Typed Arithmetic Expressions *)

(* syntax *)

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm
  | tzero : tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tiszero : tm -> tm.

Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue ttrue
  | bv_false : bvalue tfalse.

Inductive nvalue : tm -> Prop :=
  | nv_zero : nvalue tzero
  | nv_succ : forall t, nvalue t -> nvalue (tsucc t).

Definition value (t:tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.
Hint Unfold extend.

(* Operational Semantics *)

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 ==> t1' ->
      (tsucc t1) ==> (tsucc t1')
  | ST_PredZero :
      (tpred tzero) ==> tzero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tpred (tsucc t1)) ==> t1
  | ST_Pred : forall t1 t1',
      t1 ==> t1' ->
      (tpred t1) ==> (tpred t1')
  | ST_IszeroZero :
      (tiszero tzero) ==> ttrue
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tiszero (tsucc t1)) ==> tfalse
  | ST_Iszero : forall t1 t1',
      t1 ==> t1' ->
      (tiszero t1) ==> (tiszero t1')

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_IfTrue" | Case_aux c "ST_IfFalse" | Case_aux c "ST_If"
  | Case_aux c "ST_Succ" | Case_aux c "ST_PredZero"
  | Case_aux c "ST_PredSucc" | Case_aux c "ST_Pred"
  | Case_aux c "ST_IszeroZero" | Case_aux c "ST_IszeroSucc"
  | Case_aux c "ST_Iszero" ].

Hint Constructors step.

(* Normal Forms and Values *)

Notation step_normal_form := (normal_form step).

Definition stuck (t:tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck.

(* Exercise: 2 stars (some_term_is_stuck) *)

Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  exists (tiszero ttrue).
  unfold stuck. unfold step_normal_form. unfold not. split; intros; solve by inversion 3.
Qed.

(* codes from auto *)

Ltac inv H := inversion H; subst; clear H.
Ltac rwinv H1 H2 := rewrite H1 in H2; inv H2.
Ltac find_rwinv :=
  match goal with
    H1: ?E = true, H2: ?E = false |- _ => rwinv H1 H2
  end.
Ltac find_eqn :=
  match goal with
    H1: forall x, ?P x -> ?L = ?R, H2: ?P ?X |- _ =>
         rewrite (H1 X H2) in *
  end.

(* Exercise: 3 stars, advanced (value_is_nf) *)

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  unfold step_normal_form. unfold value. unfold not. intros t H contra.
  inv H.
  inversion H0; solve by inversion 2.
  induction H0. solve by inversion 2.
  apply IHnvalue. inversion contra. inversion H. exists t1'. assumption.
Qed.

(* Exercise: 3 stars, optional (step_deterministic) *)

Hint Resolve value_is_nf.

Ltac succ_on_value :=
  match goal with
    H1: nvalue ?X, H2: tsucc ?X ==> ?P |- _ =>
      inversion H2;
      assert (step_normal_form X) by eauto;
      apply ex_falso_quodlibet; eauto
  end.

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  unfold deterministic.
  intros x y1 y2 E1 E2. generalize dependent y2.
  step_cases (induction E1) Case; intros; inv E2; repeat find_eqn; eauto; try (solve by inversion 3); try(succ_on_value).
Qed.

(* Typing *)

Inductive ty : Type :=
  | TBool : ty
  | TNat : ty.

Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_True :
       |- ttrue \in TBool
  | T_False :
       |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T,
       |- t1 \in TBool ->
       |- t2 \in T ->
       |- t3 \in T ->
       |- tif t1 t2 t3 \in T
  | T_Zero :
       |- tzero \in TNat
  | T_Succ : forall t1,
       |- t1 \in TNat ->
       |- tsucc t1 \in TNat
  | T_Pred : forall t1,
       |- t1 \in TNat ->
       |- tpred t1 \in TNat
  | T_Iszero : forall t1,
       |- t1 \in TNat ->
       |- tiszero t1 \in TBool

where "'|-' t '\in' T" := (has_type t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_True" | Case_aux c "T_False" | Case_aux c "T_If"
  | Case_aux c "T_Zero" | Case_aux c "T_Succ" | Case_aux c "T_Pred"
  | Case_aux c "T_Iszero" ].

Hint Constructors has_type.

(* Examples *)

Example has_type_1 :
  |- tif tfalse tzero (tsucc tzero) \in TNat.
Proof.
  apply T_If.
    apply T_False.
    apply T_Zero.
    apply T_Succ.
      apply T_Zero.
Qed.

Example has_type_not :
  ~ (|- tif tfalse tzero ttrue \in TBool).
Proof.
  intros Contra. solve by inversion 2.  Qed.

(** **** Exercise: 1 star, optional (succ_hastype_nat__hastype_nat)  *)
Example succ_hastype_nat__hastype_nat : forall t,
  |- tsucc t \in TNat ->
  |- t \in TNat.
Proof.
  intros. inv H. assumption.
Qed.

(* Canonical forms *)

Lemma bool_canonical : forall t,
  |- t \in TBool -> value t -> bvalue t.
Proof.
  intros t HT HV.
  inversion HV; auto.

  induction H; inversion HT; auto.
Qed.

Lemma nat_canonical : forall t,
  |- t \in TNat -> value t -> nvalue t.
Proof.
  intros t HT HV.
  inversion HV.
  inversion H; subst; inversion HT.

  auto.
Qed.

(* Progress *)

Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t'.
Proof with auto.
  intros t T HT.
  has_type_cases (induction HT) Case...
  (* The cases that were obviously values, like T_True and
     T_False, were eliminated immediately by auto *)
  Case "T_If".
    right. inversion IHHT1; clear IHHT1.
    SCase "t1 is a value".
    apply (bool_canonical t1 HT1) in H.
    inversion H; subst; clear H.
      exists t2...
      exists t3...
    SCase "t1 can take a step".
      inversion H as [t1' H1].
      exists (tif t1' t2 t3)...
  Case "T_Succ".
    inversion IHHT. apply (nat_canonical t1 HT) in H...
    inversion H. eauto.
  Case "T_Pred".
    inversion IHHT. apply (nat_canonical t1 HT) in H. inversion H; eauto.
    inversion H. eauto.
  Case "T_Iszero".
    inversion IHHT. apply (nat_canonical t1 HT) in H. inversion H; eauto.
    inversion H; eauto.
Qed.

(* Type Preservation *)

Theorem preservation : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.
Proof with auto.
  intros t t' T HT HE.
  generalize dependent t'.
  has_type_cases (induction HT) Case;
         (* every case needs to introduce a couple of things *)
         intros t' HE;
         (* and we can deal with several impossible
            cases all at once *)
         try (solve by inversion).
    Case "T_If". inversion HE; subst; clear HE.
      SCase "ST_IFTrue". assumption.
      SCase "ST_IfFalse". assumption.
      SCase "ST_If". apply T_If; try assumption.
        apply IHHT1; assumption.
    Case "T_Succ". inv HE. eauto.
    Case "T_Pred". inv HE.
      SCase "ST_PredZero". eauto.
      SCase "ST_PredSucc". inversion HT. assumption.
      SCase "ST_Pred". constructor. eauto.
    Case "T_Iszero". inv HE...
Qed.

(** **** Exercise: 3 stars (preservation_alternate_proof)  *)

Theorem preservation' : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.
Proof with eauto.
  intros t t' T HT HE.
  generalize dependent T.
  step_cases (induction HE) Case; intros T HT; inv HT; eauto.
  Case "ST_PredSucc". inversion H1. assumption.
Qed.

(* Type Soundness *)

Definition multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  |- t \in T ->
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros t t' T HT P. induction P; intros [R S].
  destruct (progress x T HT); auto.
  apply IHP.  apply (preservation x y T HT H).
  unfold stuck. split; auto.   Qed.
