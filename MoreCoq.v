Require Export Poly.


(* The apply Tactic *)

Theorem silly1 : forall(n m o p : nat),
     n = m ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  (* At this point, we could finish with
     "rewrite → eq2. reflexivity." as we have
     done several times above. But we can achieve the
     same effect in a single step by using the
     apply tactic instead: *)
  apply eq2. Qed.

Theorem silly2 : forall(n m o p : nat),
     n = m ->
     (forall(q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly2a : forall(n m : nat),
     (n,n) = (m,m) ->
     (forall(q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.

(* Exercise: 2 stars, optional (silly_ex) *)

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  intros h1 h2.
  apply h1.
  apply h2.
Qed.

Theorem silly3_firsttry : forall(n : nat),
     true = beq_nat n 5 ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  simpl.
  (* Here we cannot use apply directly *)
Abort.

Theorem silly3 : forall(n : nat),
     true = beq_nat n 5 ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl. (* Actually, this simpl is unnecessary, since
            apply will perform simplification first. *)
  apply H. Qed.

(* Exercise: 3 stars (apply_exercise1) *)

SearchAbout rev.

Theorem rev_exercise1 : forall(l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l' h.
  rewrite -> h.
  symmetry.
  apply rev_involutive.
Qed.

(* The apply ... with ... Tactic *)

Example trans_eq_example : forall(a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.

Theorem trans_eq : forall(X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Example trans_eq_example' : forall(a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  (* If we simply tell Coq apply trans_eq at this point,
     it can tell (by matching the goal against the
     conclusion of the lemma) that it should instantiate X
     with [nat], n with [a,b], and o with [e,f].
     However, the matching process doesn't determine an
     instantiation for m: we have to supply one explicitly
     by adding with (m:=[c,d]) to the invocation of
     apply. *)
  apply trans_eq with [c;d]. apply eq1. apply eq2. Qed.

(* Exercise: 3 stars, optional (apply_with_exercise) *)

Example trans_eq_exercise : forall(n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p h1 h2.
  apply trans_eq with m. apply h2. apply h1. Qed.
