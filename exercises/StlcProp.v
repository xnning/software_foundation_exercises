Require Export Stlc.

Module STLCProp.
Import STLC.

(* Canonical Forms *)

Lemma canonical_forms_bool : forall t,
  empty |- t \in TBool ->
  value t ->
  (t = ttrue) \/ (t = tfalse).
Proof.
  intros t HT HVal.
  inversion HVal; intros; subst; try inversion HT; auto.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t \in (TArrow T1 T2) ->
  value t ->
  exists x u, t = tabs x T1 u.
Proof.
  intros t T1 T2 HT HVal.
  inversion HVal; intros; subst; try inversion HT; subst; auto.
  exists x0. exists t0.  auto.
Qed.

(* Progress *)

Theorem progress : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.
Proof with eauto.
  intros t T Ht.
  remember (@empty ty) as Gamma.
  has_type_cases (induction Ht) Case; subst Gamma...
  Case "T_Var".
    (* contradictory: variables cannot be typed in an
       empty context *)
    inversion H.

  Case "T_App".
    (* [t] = [t1 t2].  Proceed by cases on whether [t1] is a
       value or steps... *)
    right. destruct IHHt1...
    SCase "t1 is a value".
      destruct IHHt2...
      SSCase "t2 is also a value".
        assert (exists x0 t0, t1 = tabs x0 T11 t0).
        eapply canonical_forms_fun; eauto.
        destruct H1 as [x0 [t0 Heq]]. subst.
        exists ([x0:=t2]t0)...

      SSCase "t2 steps".
        inversion H0 as [t2' Hstp]. exists (tapp t1 t2')...

    SCase "t1 steps".
      inversion H as [t1' Hstp]. exists (tapp t1' t2)...

  Case "T_If".
    right. destruct IHHt1...

    SCase "t1 is a value".
      destruct (canonical_forms_bool t1); subst; eauto.

    SCase "t1 also steps".
      inversion H as [t1' Hstp]. exists (tif t1' t2 t3)...
Qed.

(* Exercise: 3 stars, optional (progress_from_term_ind) *)

Theorem progress' : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.
Proof.
  intros t.
  t_cases (induction t) Case; intros T Ht; auto.
  Case "tvar". inversion Ht. inversion H1.
  Case "tapp".
    inv Ht. destruct (IHt1 (TArrow T11 T) H2) as [v1 | s1].
    destruct (IHt2 T11 H4) as [v2 | s2].
    SCase "t1 value; t2 value". right.
      assert (exists x0 t0, t1 = tabs x0 T11 t0). eapply canonical_forms_fun; eauto.
      destruct H as [x0 [t0 abs]]. subst. exists ([x0:=t2] t0); eauto.
    SCase "t1 value; t2 step". right.
      inv s2. exists (tapp t1 x0). eauto.
    SCase "t1 step". right.
      inv s1. exists (tapp x0 t2); eauto.
  Case "tif".
    inv Ht. destruct (IHt1 TBool H3) as [v1 | s1].
    SCase "t1 value". right.
      assert (t1 = ttrue \/ t1 = tfalse). apply canonical_forms_bool; eauto.
      destruct H as [tt | tf]; subst. exists t2; eauto. exists t3;eauto.
    SCase "t1 step". right.
      inv s1.
      exists (tif x0 t2 t3); eauto.
Qed.

(* Preservation *)

(* Free Occurrences *)

Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tvar x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tapp t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tapp t1 t2)
  | afi_abs : forall x y T11 t12,
      y <> x  ->
      appears_free_in x t12 ->
      appears_free_in x (tabs y T11 t12)
  | afi_if1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (tif t1 t2 t3)
  | afi_if2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (tif t1 t2 t3)
  | afi_if3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (tif t1 t2 t3).

Tactic Notation "afi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "afi_var"
  | Case_aux c "afi_app1" | Case_aux c "afi_app2"
  | Case_aux c "afi_abs"
  | Case_aux c "afi_if1" | Case_aux c "afi_if2"
  | Case_aux c "afi_if3" ].

Hint Constructors appears_free_in.

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

(* Substitution *)

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.

  Proof.
  intros x t T Gamma H H0. generalize dependent Gamma.
  generalize dependent T.
  afi_cases (induction H) Case;
         intros; try solve [inversion H0; eauto].
  Case "afi_abs".
    inversion H1; subst.
    apply IHappears_free_in in H7.
    rewrite extend_neq in H7; assumption.
Qed.
(* Exercise: 2 stars, optional (typable_empty__closed) *)

Corollary typable_empty__closed : forall t T,
    empty |- t \in T  ->
    closed t.
Proof.
  unfold closed; unfold not; intros t T Ht x contra.
  generalize dependent T; afi_cases(induction contra) Case; intros T Ht; inv Ht; try(eapply IHcontra); eauto.
  Case "afi_var"; solve by inversion.
  Case "afi_abs".
    assert (exists xt, extend \empty y0 T11 x0 = Some xt).
      eapply free_in_context; eauto.
    inv H0. rewrite (extend_neq) in H1. inversion H1. assumption.
  Unshelve. auto.
Qed.

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |- t \in T  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in T.
Proof with eauto.
  intros.
  generalize dependent Gamma'.
  has_type_cases (induction H) Case; intros; auto.
  Case "T_Var".
    apply T_Var. rewrite <- H0...
  Case "T_Abs".
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    (* the only tricky step... the [Gamma'] we use to
       instantiate is [extend Gamma x T11] *)
    unfold extend. destruct (eq_id_dec x0 x1)...
  Case "T_App".
    apply T_App with T11...
Qed.

Lemma substitution_preserves_typing : forall Gamma x U t v T,
     extend Gamma x U |- t \in T ->
     empty |- v \in U   ->
     Gamma |- [x:=v]t \in T.
Proof with eauto.
  intros Gamma x U t v T Ht Ht'.
  generalize dependent Gamma. generalize dependent T.
  t_cases (induction t) Case; intros T Gamma H;
    (* in each case, we'll want to get at the derivation of H *)
    inversion H; subst; simpl...
  Case "tvar".
    rename i into y. destruct (eq_id_dec x y).
    SCase "x=y".
      subst.
      rewrite extend_eq in H2.
      inversion H2; subst. clear H2.
                  eapply context_invariance... intros x Hcontra.
      destruct (free_in_context _ _ T empty Hcontra) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
      apply T_Var. rewrite extend_neq in H2...
  Case "tabs".
    rename i into y. apply T_Abs.
    destruct (eq_id_dec x y).
    SCase "x=y".
      eapply context_invariance...
      subst.
      intros x Hafi. unfold extend.
      destruct (eq_id_dec y x)...
    SCase "x<>y".
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold extend.
      destruct (eq_id_dec y z)...
      subst. rewrite neq_id...
Qed.

(* Main Theorem *)

Theorem preservation : forall t t' T,
     empty |- t \in T  ->
     t ==> t'  ->
     empty |- t' \in T.

  Proof with eauto.
  remember (@empty ty) as Gamma.
  intros t t' T HT. generalize dependent t'.
  has_type_cases (induction HT) Case;
       intros t' HE; subst Gamma; subst;
       try solve [inversion HE; subst; auto].
  Case "T_App".
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and [eauto] takes care of them *)
    SCase "ST_AppAbs".
      apply substitution_preserves_typing with T11...
      inversion HT1...
Qed.

(* Type Soundness *)

(* Exercise: 2 stars, optional (type_soundness) *)

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.


Corollary soundness : forall t t' T,
  empty |- t \in T ->
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti.
  Case "mult_refl".
    apply progress in Hhas_type. destruct Hhas_type as [v1 | s1].
    apply Hnot_val; auto. apply Hnf; auto.
  Case "mult_step".
    apply IHHmulti;(try assumption). eapply preservation; eauto.
Qed.