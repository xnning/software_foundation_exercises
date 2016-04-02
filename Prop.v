Require Export Logic.

(* Inductively Defined Propositions *)

(* a function. given nat. return Prop.  *)
Definition even (n:nat) : Prop :=
  evenb n = true.

(* a family of propositions "indexed by" natural numbers. *)
Inductive ev : nat -> Prop :=
    (* evidence for 0 is even *)
  | ev_0 : ev O
    (* evidence for S (S n) is even by giving evidence for n *)
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

(* Exercise: 1 star (double_even) *)
Theorem double_even : forall n,
  ev (double n).
Proof.
  induction n as [| n'].
  simpl. apply ev_0.
  simpl. apply (ev_SS (double n') IHn').
Qed.

(* Exercise: 1 star (varieties_of_beauty) *)
(* infinite since we have 0 *)

Inductive beautiful : nat -> Prop :=
  b_0 : beautiful 0
| b_3 : beautiful 3
| b_5 : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).

Theorem three_is_beautiful: beautiful 3.
Proof.
   apply b_3.
Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
   apply b_sum with (n:=3) (m:=5).
   apply b_3.
   apply b_5.
Qed.

Theorem beautiful_plus_eight: forall n, beautiful n -> beautiful (8+n).
Proof.
  intros n B.
  apply b_sum with (n:=8) (m:=n).
  apply eight_is_beautiful.
  apply B.
Qed.

(* Exercise: 2 stars (b_times2) *)
Theorem b_times2: forall n, beautiful n -> beautiful (2×n).
Proof.
  intros n B.
  simpl.
  apply b_sum with (n:=n) (m:=n+0).
  apply B. apply b_sum with (n:=n) (m:=0). apply B. apply b_0.
Qed.

(* Exercise: 3 stars (b_timesm) *)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m×n).
Proof.
  intros n m B.
  induction m as [| m'].
  simpl. apply b_0.
  simpl. apply b_sum. apply B. apply IHm'.
Qed.

(* Using Evidence in Proofs *)

(* Induction over Evidence *)
Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

(* Exercise: 1 star (gorgeous_plus13) *)

Theorem gorgeous_plus13: forall n,
  gorgeous n ->  gorgeous (13+n).
Proof.
  intros n H.
  apply g_plus3. apply g_plus5. apply g_plus5. apply H.
Qed.

Theorem gorgeous__beautiful_FAILED : forall n,
  gorgeous n -> beautiful n.
Proof.
   intros. induction n as [| n'].
   Case "n = 0". apply b_0.
   Case "n = S n'". (* We are stuck! *)
Abort.

Theorem gorgeous__beautiful : forall n,
  gorgeous n -> beautiful n.
Proof.
   intros n H.
   induction H as [|n'|n'].
   Case "g_0".
       apply b_0.
   Case "g_plus3".
       apply b_sum. apply b_3.
       apply IHgorgeous.
   Case "g_plus5".
       apply b_sum. apply b_5. apply IHgorgeous.
Qed.

(* Exercise: 2 stars (gorgeous_sum) *)

Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  intros.
  induction H as [|n'|n'].
  apply H0.
  rewrite <- plus_assoc. apply g_plus3. apply IHgorgeous.
  rewrite <- plus_assoc. apply g_plus5. apply IHgorgeous.
Qed.

(* Exercise: 3 stars, advanced (beautiful__gorgeous) *)

Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
  intros.
  induction H as [| | | n1 n2].
  Case "n = 0". apply g_0.
  Case "n = 3". apply g_plus3. apply g_0.
  Case "n = 5". apply g_plus5. apply g_0.
  Case "n = n1 + n2". apply gorgeous_sum. apply IHbeautiful1. apply IHbeautiful2.
Qed.

(* Exercise: 3 stars, optional (g_times2) *)
Lemma helper_g_times2 : forall x y z, x + (z + y) = z + x + y.
Proof.
  intros.
  rewrite -> plus_assoc.
  rewrite -> (plus_comm x z).
  reflexivity.
Qed.

Theorem g_times2: forall n, gorgeous n -> gorgeous (2×n).
Proof.
   intros n H. simpl. rewrite <- plus_n_O.
   induction H.
   Case "n = 0". apply g_0.
   Case "n = 3 + n".
     rewrite helper_g_times2. apply g_plus3 in IHgorgeous.
     apply g_plus3 in IHgorgeous. apply IHgorgeous.
   Case "n = 5 + n".
     rewrite helper_g_times2. apply g_plus5 in IHgorgeous.
     apply g_plus5 in IHgorgeous. apply IHgorgeous.
Qed.

Theorem ev__even : forall n,
  ev n -> even n.
Proof.
  intros n E. induction E as [| n' E'].
  Case "E = ev_0".
    unfold even. reflexivity.
  Case "E = ev_SS n' E'".
    unfold even. apply IHE'.
Qed.

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof.
  intros.
  induction H.
  apply H0.
  rewrite -> plus_Sn_m.
  rewrite -> plus_Sn_m.
  apply ev_SS. apply IHev.
Qed.

(* Inversion on Evidence *)

Theorem ev_minus2: forall n, ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0.
  Case "E = ev_SS n' E'". simpl. apply E'. Qed.

Theorem SSev__even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  apply E'. Qed.

(* The Inversion Tactic Revisited *)

(* Exercise: 1 star (inversion_practice) *)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros.
  inversion H.
  inversion H1.
  apply H3.
Qed.

Theorem even5_nonsense :
  ev 5 ->  2 + 2 = 9.
Proof.
  intros.
  inversion H. inversion H1. inversion H3.
Qed.

(* Exercise: 3 stars, advanced (ev_ev__ev) *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m H1 H2.
  induction H2 as[ |n'].
  Case "n = 0". simpl in H1. apply H1.
  Case "n = S (S n')".
    inversion H1. apply IHev in H0. apply H0.
Qed.

(* Exercise: 3 stars, optional (ev_plus_plus) *)
Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros.
  assert (ev (n + m + (n + p))). apply ev_sum. apply H. apply H0.
  rewrite plus_swap in H1. rewrite plus_assoc in H1. rewrite plus_assoc in H1.
  rewrite <- double_plus in H1. rewrite <- plus_assoc in H1.
  apply ev_ev__ev with (n:= double n). apply H1. apply double_even.
Qed.

(* Discussion and Variations *)

(* Parameterized Data Structures *)

Inductive ev_list {X:Type} : list X -> Prop :=
  | el_nil : ev_list []
  | el_cc : forall x y l, ev_list l -> ev_list (x :: y :: l).

Lemma ev_list__ev_length: forall X (l : list X), ev_list l -> ev (length l).
Proof.
    intros X l H. induction H.
    Case "el_nil". simpl. apply ev_0.
    Case "el_cc". simpl. apply ev_SS. apply IHev_list.
Qed.

Lemma ev_length__ev_list: forall X n, ev n -> forall(l : list X), n = length l -> ev_list l.
Proof.
  intros X n H.
  induction H.
  Case "ev_0". intros l H. destruct l.
    SCase "[]". apply el_nil.
    SCase "x::l". inversion H.
  Case "ev_SS". intros l H2. destruct l.
    SCase "[]". inversion H2. destruct l.
    SCase "[x]". inversion H2.
    SCase "x :: x0 :: l". apply el_cc. apply IHev. inversion H2. reflexivity.
Qed.

(* Exercise: 4 stars (palindromes) *)

Inductive pal {X: Type}: list X -> Prop :=
  | pal_nil : pal []
  | pal_singleton : forall x, pal [x]
  | pal_cc : forall (x:X) l, pal l -> pal (x :: snoc l x).

Theorem pal_app_rev : forall X (l:list X), pal (l ++ rev l).
Proof.
  intros.
  induction l as [| x l'].
  Case "l = []". simpl. apply pal_nil.
  Case "l = x :: l'". simpl. rewrite <- snoc_with_append.
    apply pal_cc. apply IHl'.
Qed.

Theorem pal_rev : forall X (l:list X), pal l -> l = rev l.
Proof.
  intros.
  induction H.
  Case "l = []". reflexivity.
  Case "l = [x]". reflexivity.
  Case "l = x :: snoc l x".
    simpl. rewrite rev_snoc. simpl.
    rewrite <- IHpal. reflexivity.
Qed.

