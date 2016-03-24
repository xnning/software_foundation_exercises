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

(* The inversion tactic *)

Theorem eq_add_S : forall(n m : nat),
     S n = S m ->
     n = m.
Proof.
  intros n m eq. inversion eq. reflexivity. Qed.

Theorem silly4 : forall(n m : nat),
     [n] = [m] ->
     n = m.
Proof.
  intros n o eq. inversion eq. reflexivity. Qed.

Theorem silly5 : forall(n m o : nat),
    [n;m] = [o;o]->
    [n] = [m].
Proof.
  intros n m o eq. inversion eq. reflexivity. Qed.

(* Exercise: 1 star (sillyex1) *)

Example sillyex1 : forall(X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  intros X x y z l j h1 h2.
  inversion h2.
  reflexivity.
Qed.

Theorem silly6 : forall(n : nat),
     S n = O ->
     2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Theorem silly7 : forall(n m : nat),
     false = true ->
     [n] = [m].
Proof.
  intros n m contra. inversion contra. Qed.

(* Exercise: 1 star (sillyex2) *)

Example sillyex2 : forall(X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof.
  intros X x y z l j h1 h2.
  inversion h1.
Qed.

Theorem f_equal : forall(A B : Type) (f: A -> B) (x y: A),
    x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.

(* Exercise: 2 stars, optional (practice) *)

Theorem beq_nat_0_l : forall n,
   beq_nat 0 n = true -> n = 0.
Proof.
  intros n h.
  destruct n as [ | n'].
  reflexivity.
  inversion h.
Qed.

Theorem beq_nat_0_r : forall n,
   beq_nat n 0 = true -> n = 0.
Proof.
  intros n h.
  destruct n as [ | n'].
  reflexivity.
  inversion h.
Qed.

(* Using Tactics on Hypotheses *)

Theorem S_inj : forall(n m : nat) (b : bool),
     beq_nat (S n) (S m) = b ->
     beq_nat n m = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.

Theorem silly3' : forall(n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
     true = beq_nat n 5 ->
     true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H. Qed.

(* Exercise: 3 stars (plus_n_n_injective) *)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    intros m h.
    destruct m as [| m'].
    reflexivity.
    inversion h.
  Case "n = S n'".
    intros m h.
    destruct m as [| m'].
    inversion h.
    apply f_equal.
    apply IHn'.
    simpl in h.
    rewrite <- plus_n_Sm in h.
    rewrite <- plus_n_Sm in h.
    inversion h.
    reflexivity.
Qed.
