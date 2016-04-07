Require Export Prop1.

(* Existential Quantification *)

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall(witness:X), P witness -> ex X P.

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.

Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

Example exists_example_1 : exists n, n + (n × n) = 6.
Proof.
  apply ex_intro with (witness:=2).
  reflexivity. Qed.

Example exists_example_1' : exists n, n + (n × n) = 6.
Proof.
  exists 2.
  reflexivity. Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm].
  exists(2 + m).
  apply Hm. Qed.

Lemma exists_example_3 :
  exists (n:nat), even n /\ beautiful n.
Proof.
  exists 8.
  split.
  unfold even. simpl. reflexivity.
  apply b_sum with (n:=3) (m:=5).
  apply b_3. apply b_5.
Qed.

(* Exercise: 1 star (dist_not_exists) *)
Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P Fa.
  unfold not.
  intros Ex.
  inversion Ex as [x h].
  apply h.
  apply Fa.
Qed.

(* Exercise: 3 stars, optional (not_exists_dist) *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold excluded_middle.
  unfold not.
  intros.
  destruct (H (P x)) as [px| npx].
  apply px.
  assert (exists x:X, P x -> False). exists x. apply npx.
  apply H0 in H1.
  inversion H1.
Qed.

(* Exercise: 2 stars (dist_exists_or) *)
Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros.
  split.
  Case "left".
  intros.
  inversion H.
  destruct H0.
  left. exists witness. apply H0.
  right. exists witness. apply H0.
  Case "right".
  intros.
  destruct H as [px | qx].
  inversion px.
  exists witness. left. apply H.
  inversion qx.
  exists witness. right. apply H.
Qed.
