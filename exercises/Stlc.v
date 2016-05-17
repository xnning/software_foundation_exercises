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

Theorem substi_correct : forall s x t t',
  [x:=s]t = t' <-> substi s x t t'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)
