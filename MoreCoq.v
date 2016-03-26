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

(* Varying the Induction Hypothesis *)

Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction n as [| n'].
  Case "n = O". simpl. intros eq. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion eq.
  Case "n = S n'". intros eq. destruct m as [| m'].
    SCase "m = O". inversion eq.
    SCase "m = S m'". apply f_equal.
      (* Here we are stuck.  The induction hypothesis, IHn', does
         not give us n' = m' -- there is an extra S in the
         way -- so the goal is not provable. *)
      Abort.

Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = O". simpl. intros m eq. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion eq.
  Case "n = S n'".
    (* Notice that both the goal and the induction
       hypothesis have changed: the goal asks us to prove
       something more general (i.e., to prove the
       statement for _every_ m), but the IH is
       correspondingly more flexible, allowing us to
       choose any m we like when we apply the IH.  *)
    intros m eq.
    (* Now we choose a particular m and introduce the
       assumption that double n = double m.  Since we
       are doing a case analysis on n, we need a case
       analysis on m to keep the two "in sync." *)
    destruct m as [| m'].
    SCase "m = O".
      (* The 0 case is trivial *)
      inversion eq.
    SCase "m = S m'".
      apply f_equal.
      (* At this point, since we are in the second
         branch of the destruct m, the m' mentioned
         in the context at this point is actually the
         predecessor of the one we started out talking
         about.  Since we are also in the S branch of
         the induction, this is perfect: if we
         instantiate the generic m in the IH with the
         m' that we are talking about right now (this
         instantiation is performed automatically by
         apply), then IHn' gives us exactly what we
         need to finish the proof. *)
      apply IHn'. inversion eq. reflexivity. Qed.

(* Exercise: 2 stars (beq_nat_true) *)

Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0".
    intros m eq.
    destruct m.
    reflexivity.
    inversion eq.
  Case "n = S n'".
    intros m eq.
    destruct m as [| m'].
    inversion eq.
    apply f_equal.
    apply IHn'.
    inversion eq.
    reflexivity.
Qed.

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m'].
  Case "m = O". simpl. intros eq. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "m = S m'". intros eq. destruct n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'". apply f_equal.
        (* Stuck again here, just like before. *)
Abort.

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
  (* Now n is back in the goal and we can do induction on
     m and get a sufficiently general IH. *)
  induction m as [| m'].
  Case "m = O". simpl. intros n eq. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "m = S m'". intros n eq. destruct n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'". apply f_equal.
      apply IHm'. inversion eq. reflexivity. Qed.


Theorem length_snoc' : forall(X : Type) (v : X)
                              (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n.
Proof.
  intros X v l. induction l as [| v' l'].
  Case "l = []".
    intros n eq. rewrite <- eq. reflexivity.
  Case "l = v' :: l'".
    intros n eq. simpl. destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      apply f_equal. apply IHl'. inversion eq. reflexivity. Qed.

Theorem length_snoc_bad : forall(X : Type) (v : X)
                              (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n.
Proof.
  intros X v l n eq. induction l as [| v' l'].
  Case "l = []".
    rewrite <- eq. reflexivity.
  Case "l = v' :: l'".
    simpl. destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      apply f_equal. Abort. (* apply IHl'. *) (* The IH doesn't apply! *)

(* Exercise: 3 stars (gen_dep_practice) *)

Theorem index_after_last: forall(n : nat) (X : Type) (l : list X),
     length l = n ->
     index n l = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [| h t].
  Case "l = []".
    intros n eq.
    destruct n as [| n'].
    SCase "n = 0". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "l = h :: t".
    intros n eq.
    destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      simpl.
      apply IHt.
      inversion eq.
      reflexivity.
Qed.

(* Exercise: 3 stars, optional (gen_dep_practice_more) *)

Theorem length_snoc''' : forall(n : nat) (X : Type)
                              (v : X) (l : list X),
     length l = n ->
     length (snoc l v) = S n.
Proof.
  intros n X v l.
  generalize dependent n.
  induction l as [| h t].
  Case "l = []".
    intros n eq.
    destruct n.
    SCase "n = 0". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "l = h :: t".
    intros n eq.
    destruct n.
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      simpl.
      apply f_equal.
      apply IHt.
      inversion eq.
      reflexivity.
Qed.

(* Exercise: 3 stars, optional (app_length_cons) *)

Theorem app_length_cons : forall(X : Type) (l1 l2 : list X)
                                  (x : X) (n : nat),
     length (l1 ++ (x :: l2)) = n ->
     S (length (l1 ++ l2)) = n.
Proof.
  intros X l1 l2 x.
  induction l1 as [| h t].
  Case "l1 = []".
    intros n eq.
    destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'". simpl. simpl in eq. apply eq.
  Case "l1 = h :: t".
    intros n eq.
    destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      apply f_equal.
      simpl.
      apply IHt.
      inversion eq.
      reflexivity.
Qed.

(* Exercise: 4 stars, optional (app_length_twice) *)

Theorem app_length_cons2 : forall(X:Type) (h:X) (t:list X),
      length (t ++ h :: t) = S (length (t ++ t)).
Proof.
  intros X h t.
  symmetry.
  apply app_length_cons with h.
  reflexivity.
Qed.

Theorem app_length_twice : forall(X:Type) (n:nat) (l:list X),
     length l = n ->
     length (l ++ l) = n + n.
Proof.
  intros X n l.
  generalize dependent n.
  induction l as [| h t].
  Case "l = []".
    intros n eq.
    destruct n as [|n'].
    SCase "n = 0". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "l = h :: t".
    intros n eq.
    destruct n as [|n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      simpl.
      apply f_equal.
      rewrite -> app_length_cons2.
      rewrite <- plus_n_Sm.
      apply f_equal.
      apply IHt.
      simpl in eq.
      inversion eq.
      reflexivity.
Qed.

(* Exercise: 3 stars, optional (double_induction) *)

Theorem double_induction: forall(P : nat -> nat -> Prop),
  P 0 0 ->
  (forall m, P m 0 -> P (S m) 0) ->
  (forall n, P 0 n -> P 0 (S n)) ->
  (forall m n, P m n -> P (S m) (S n)) ->
  forall m n, P m n.
Proof.
  intros P.
  intros h1 h2 h3 h4.
  intros m.
  induction m as [| m'].
  Case "m = 0".
    induction n as [| n'].
    apply h1.
    apply h3. apply IHn'.
  Case "m = S m'".
    induction n as [| n'].
    apply h2. apply IHm'.
    apply h4. apply IHm'.
Qed.

(* Using destruct on Compound Expressions *)

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall(n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (beq_nat n 3).
    Case "beq_nat n 3 = true". reflexivity.
    Case "beq_nat n 3 = false". destruct (beq_nat n 5).
      SCase "beq_nat n 5 = true". reflexivity.
      SCase "beq_nat n 5 = false". reflexivity. Qed.

(* Exercise: 1 star (override_shadow) *)

Theorem override_shadow : forall(X:Type) x1 x2 k1 k2 (f : nat -> X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  intros X x1 x2 k1 k2 f.
  unfold override.
  destruct (beq_nat k1 k2).
    Case "beq_nat k1 k2 = true". reflexivity.
    Case "beq_nat k1 k2 = false". reflexivity.
Qed.

(* Exercise: 3 stars, optional (combine_split) *)

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [| (h1, h2) t].
  Case "l = []".
    intros l1 l2 h.
    inversion h.
    reflexivity.
  Case "l = h :: t".
    intros l1 l2 h.
    inversion h.
    destruct (split t) as (t1, t2).
    inversion H0.
    simpl.
    apply f_equal.
    apply IHt.
    reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

Theorem sillyfun1_odd_FAILED : forall(n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3).
  (* stuck... *)
Abort.

Theorem sillyfun1_odd : forall(n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3) eqn:Heqe3.
  (* Now we have the same state as at the point where we got stuck
    above, except that the context contains an extra equality
    assumption, which is exactly what we need to make progress. *)
    Case "e3 = true". apply beq_nat_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    Case "e3 = false".
     (* When we come to the second equality test in the body of the
       function we are reasoning about, we can use eqn: again in the
       same way, allow us to finish the proof. *)
      destruct (beq_nat n 5) eqn:Heqe5.
        SCase "e5 = true".
          apply beq_nat_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        SCase "e5 = false". inversion eq. Qed.

(* Exercise: 2 stars (destruct_eqn_practice) *)

Theorem bool_fn_applied_thrice :
  forall(f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b eqn:bh.
    destruct (f true) eqn: ft.
      rewrite -> ft.
      apply ft.
      destruct (f false) eqn: ff.
        apply ft.
        apply ff.
    destruct (f false) eqn:ff.
      destruct (f true) eqn: ft.
        apply ft.
        apply ff.
      rewrite ff.
      apply ff.
Qed.

(* Exercise: 2 stars (override_same) *)

Theorem override_same : forall(X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 ->
  (override f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f h.
  unfold override.
  destruct (beq_nat k1 k2) eqn: hk.
  apply beq_nat_true in hk.
  rewrite <- hk.
  symmetry.
  apply h.
  reflexivity.
Qed.