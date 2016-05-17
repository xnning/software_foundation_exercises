Require Export Types.

(* The Simply Typed Lambda-Calculus *)

(* Syntax *)

Module STLC.

Inductive ty : Type :=
  | TBool  : ty
  | TArrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp"
  | Case_aux c "tabs" | Case_aux c "ttrue"
  | Case_aux c "tfalse" | Case_aux c "tif" ].

Definition x := (Id 0).
Definition y := (Id 1).
Definition z := (Id 2).
Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

(** [idB = \x:Bool. x] *)

Notation idB :=
  (tabs x TBool (tvar x)).

(** [idBB = \x:Bool->Bool. x] *)

Notation idBB :=
  (tabs x (TArrow TBool TBool) (tvar x)).

(** [idBBBB = \x:(Bool->Bool) -> (Bool->Bool). x] *)

Notation idBBBB :=
  (tabs x (TArrow (TArrow TBool TBool)
                      (TArrow TBool TBool))
    (tvar x)).

(** [k = \x:Bool. \y:Bool. x] *)

Notation k := (tabs x TBool (tabs y TBool (tvar x))).

(** [notB = \x:Bool. if x then false else true] *)

Notation notB := (tabs x TBool (tif (tvar x) tfalse ttrue)).

(* Operational Semantics *)

(* Values *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  | v_true :
      value ttrue
  | v_false :
      value tfalse.

Hint Constructors value.

(* Substitution *)

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' =>
      if eq_id_dec x x' then s else t
  | tabs x' T t1 =>
      tabs x' T (if eq_id_dec x x' then t1 else ([x:=s] t1))
  | tapp t1 t2 =>
      tapp ([x:=s] t1) ([x:=s] t2)
  | ttrue =>
      ttrue
  | tfalse =>
      tfalse
  | tif t1 t2 t3 =>
      tif ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

(* Exercise: 3 stars (substi) *)

Inductive substi (s:tm) (x:id) : tm -> tm -> Prop :=
  | s_var1 : substi s x (tvar x) s
  | s_var2 : forall y:id, (x <> y) -> substi s x (tvar y) (tvar y)
  | s_abs1 : forall T t1, substi s x (tabs x T t1) (tabs x T t1)
  | s_abs2: forall y T t1 t2, (x <> y) -> substi s x t1 t2 -> substi s x (tabs y T t1) (tabs y T t2)
  | s_app : forall t1 t2 t1' t2', substi s x t1 t1' -> substi s x t2 t2' -> substi s x (tapp t1 t2) (tapp t1' t2')
  | s_true: substi s x ttrue ttrue
  | s_false :substi s x tfalse tfalse
  | t_if: forall t1 t2 t3 t1' t2' t3', substi s x t1 t1' -> substi s x t2 t2' -> substi s x t3 t3' -> substi s x (tif t1 t2 t3) (tif t1' t2' t3')
.

Hint Constructors substi.

Hint Resolve eq_id.
Hint Resolve neq_id.
Hint Unfold subst.

Theorem substi_correct : forall s x t t',
  [x:=s]t = t' <-> substi s x t t'.
Proof.
  intros s x t t'. split.
  Case "->"; generalize dependent t'; induction t; intros t' H; simpl in H; try(destruct (eq_id_dec x i));subst; auto.
  Case "<-"; intros; induction H;subst; simpl; try(rewrite eq_id); try(rewrite neq_id); auto.
Qed.

(* Reduction *)

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         tapp t1 t2 ==> tapp t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         tapp v1 t2 ==> tapp v1  t2'
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1"
  | Case_aux c "ST_App2" | Case_aux c "ST_IfTrue"
  | Case_aux c "ST_IfFalse" | Case_aux c "ST_If" ].

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

(* example *)

Lemma step_example1 :
  (tapp idBB idB) ==>* idB.
Proof.
  eapply multi_step.
    apply ST_AppAbs.
    apply v_abs.
  simpl.
  apply multi_refl.  Qed.

Lemma step_example2 :
  (tapp idBB (tapp idBB idB)) ==>* idB.
Proof.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto.
  eapply multi_step.
    apply ST_AppAbs. simpl. auto.
  simpl. apply multi_refl.  Qed.

Lemma step_example3 :
  tapp (tapp idBB notB) ttrue ==>* tfalse.
Proof.
  eapply multi_step.
    apply ST_App1. apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_IfTrue. apply multi_refl.  Qed.

Lemma step_example4 :
  tapp idBB (tapp notB ttrue) ==>* tfalse.
Proof.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_IfTrue.
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  apply multi_refl.  Qed.

Lemma step_example1' :
  (tapp idBB idB) ==>* idB.
Proof. normalize.  Qed.

Lemma step_example2' :
  (tapp idBB (tapp idBB idB)) ==>* idB.
Proof.
  normalize.
Qed.

Lemma step_example3' :
  tapp (tapp idBB notB) ttrue ==>* tfalse.
Proof. normalize.  Qed.

Lemma step_example4' :
  tapp idBB (tapp notB ttrue) ==>* tfalse.
Proof. normalize.  Qed.

(* Exercise: 2 stars (step_example3) *)

Lemma step_example5 :
       (tapp (tapp idBBBB idBB) idB)
  ==>* idB.
Proof.
  normalize.
Qed.

Lemma step_example5' :
       (tapp (tapp idBBBB idBB) idB)
  ==>* idB.
Proof.
  eapply multi_step. eauto.
  eapply multi_step. simpl. eauto.
  simpl. eauto.
Qed.

(* Typing *)

(* context *)

Module PartialMap.

Definition partial_map (A:Type) := id -> option A.

Definition empty {A:Type} : partial_map A := (fun _ => None).

Definition extend {A:Type} (Gamma : partial_map A) (x:id) (T : A) :=
  fun x' => if eq_id_dec x x' then Some T else Gamma x'.

Lemma extend_eq : forall A (ctxt: partial_map A) x T,
  (extend ctxt x T) x = Some T.
Proof.
  intros. unfold extend. rewrite eq_id. auto.
Qed.

Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
  x2 <> x1 ->
  (extend ctxt x2 T) x1 = ctxt x1.
Proof.
  intros. unfold extend. rewrite neq_id; auto.
Qed.

End PartialMap.

Definition context := partial_map ty.

(* Typing Relation *)

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      extend Gamma x T11 |- t12 \in T12 ->
      Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 ->
      Gamma |- t2 \in T11 ->
      Gamma |- tapp t1 t2 \in T12
  | T_True : forall Gamma,
       Gamma |- ttrue \in TBool
  | T_False : forall Gamma,
       Gamma |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in TBool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- tif t1 t2 t3 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs"
  | Case_aux c "T_App" | Case_aux c "T_True"
  | Case_aux c "T_False" | Case_aux c "T_If" ].

Hint Constructors has_type.

(* Examples *)

Example typing_example_1 :
  empty |- tabs x TBool (tvar x) \in TArrow TBool TBool.
Proof.
  apply T_Abs. apply T_Var. reflexivity.  Qed.

Example typing_example_1' :
  empty |- tabs x TBool (tvar x) \in TArrow TBool TBool.
Proof. auto.  Qed.

Example typing_example_2 :
  empty |-
    (tabs x TBool
       (tabs y (TArrow TBool TBool)
          (tapp (tvar y) (tapp (tvar y) (tvar x))))) \in
    (TArrow TBool (TArrow (TArrow TBool TBool) TBool)).
Proof with auto using extend_eq.
  apply T_Abs.
  apply T_Abs.
  eapply T_App. apply T_Var...
  eapply T_App. apply T_Var...
  apply T_Var...
Qed.

(* Exercise: 2 stars, optional (typing_example_2_full) *)

Example typing_example_2_full :
  empty |-
    (tabs x TBool
       (tabs y (TArrow TBool TBool)
          (tapp (tvar y) (tapp (tvar y) (tvar x))))) \in
    (TArrow TBool (TArrow (TArrow TBool TBool) TBool)).
Proof with auto.
  apply T_Abs.
  apply T_Abs.
  eapply T_App. apply T_Var. eapply extend_eq.
  eapply T_App. apply T_Var. eapply extend_eq.
  eapply T_Var. eapply extend_neq. intros contra. solve by inversion.
Qed.

(* Exercise: 2 stars (typing_example_3) *)

Lemma extend_find: forall A (ctxt: partial_map A) x2 x1 r T,
  x2 <> x1 ->
  ctxt x1 = r ->
  (extend ctxt x2 T) x1 = r.
Proof.
  intros. subst. apply extend_neq. assumption.
Qed.

Example typing_example_3 :
  exists T,
    empty |-
      (tabs x (TArrow TBool TBool)
         (tabs y (TArrow TBool TBool)
            (tabs z TBool
               (tapp (tvar y) (tapp (tvar x) (tvar z)))))) \in
      T.
Proof with auto.
  eapply ex_intro. repeat (apply T_Abs). eapply T_App.
  apply T_Var. eapply extend_find. intros H. solve by inversion. apply extend_eq.
  eapply T_App.
  eapply T_Var. eapply extend_find. intros H. solve by inversion.
  eapply extend_find. intros H. solve by inversion.
  apply extend_eq.
  eapply T_Var. apply extend_eq.
Qed.

Example typing_nonexample_1 :
  ~ exists T,
      empty |-
        (tabs x TBool
            (tabs y TBool
               (tapp (tvar x) (tvar y)))) \in
        T.
Proof.
  intros Hc. inversion Hc.
  (* The [clear] tactic is useful here for tidying away bits of
     the context that we're not going to need again. *)
  inversion H. subst. clear H.
  inversion H5. subst. clear H5.
  inversion H4. subst. clear H4.
  inversion H2. subst. clear H2.
  inversion H5. subst. clear H5.
  (* rewrite extend_neq in H1. rewrite extend_eq in H1. *)
  inversion H1.  Qed.

(* Exercise: 3 stars, optional (typing_nonexample_3) *)

Example typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |-
          (tabs x S
             (tapp (tvar x) (tvar x))) \in
          T).
Proof.
  intros contra.
  inv contra. inv H.
  inv H0. inv H5. inv H2. inv H1. inv H4. inversion H1. clear H1. induction T11; induction T12; try(solve by inversion 3).
  apply IHT11_1. inversion H0. rewrite <- H2 in *. rewrite H1. assumption.
  apply IHT11_1. inversion H0. rewrite <- H2 in *. rewrite H1. assumption.
Qed.
End STLC.
