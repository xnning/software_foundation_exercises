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

(* Exercise: 5 stars, optional (palindrome_converse) *)

Fixpoint init {X: Type} (l: list X) : list X :=
  match l with
  | nil => nil
  | h :: t => match t with
             | nil => nil
             | th :: t2 => h :: init t
             end
  end.

Example test_init1 : init [1;2;3;4] = [1;2;3].
reflexivity. Qed.
Example test_init2 : init (@nil nat) = [].
reflexivity. Qed.

Fixpoint tail {X: Type} (l: list X) : list X :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_tail1 : tail [1;2;3;4] = [2;3;4].
reflexivity. Qed.
Example test_tail2 : tail (@nil nat) = [].
reflexivity. Qed.

Fixpoint last {X: Type} (l: list X) : option X :=
  match l with
  | nil => None
  | h :: t => match t with
             | nil => Some h
             | th :: t2 => last t
             end
  end.

Example test_last1 : last [1;2;3;4] = Some 4.
reflexivity. Qed.
Example test_last2 : last (@nil nat) = None.
reflexivity. Qed.

Theorem last_non_nil : forall X (l:list X) (h:X) (t: list X),
    l = h :: t -> last l <> None.
Proof.
  intros X l.
  induction l as [ |h t].
  intros. inversion H.
  intros. simpl. destruct t eqn:dt.
    unfold not. intros H1. inversion H1.
    apply IHt with (h:=x) (t:=l).
    reflexivity.
Qed.

Theorem last_snoc : forall X (l:list X) (x:X),
    last (snoc l x) = Some x.
Proof.
  intros.
  induction l as [| h t].
  reflexivity.
  simpl. destruct (snoc t x). inversion IHt. apply IHt.
Qed.

Theorem rev_last : forall X (l:list X) (h x:X) (t:list X),
    l = h :: t -> l = rev l -> last l = Some x -> h = x.
Proof.
  intros.
  rewrite H in H0.
  simpl in H0.
  rewrite H in H1. rewrite H0 in H1.
  rewrite last_snoc in H1. inversion H1. reflexivity.
Qed.

Theorem rev_trans :forall X (l: list X) (h h2 x: X) (t t2:list X),
    l = h :: t -> last l = Some x -> t = h2 :: t2 -> last t = Some x.
Proof.
  intros.
  rewrite H in H0. rewrite H1 in H0.
  simpl in H0.
  rewrite H1. simpl. apply H0.
Qed.

Theorem init_tial : forall X (l: list X) (x: X),
    last l = Some x -> l = (init l ) ++ [x].
Proof.
  intros.
  induction l as [ | h t].
  inversion H.
  simpl.
  destruct t as [| h2 t2].
  inversion H. simpl. reflexivity.
  simpl. apply f_equal.
  apply IHt.
  apply rev_trans with (l:=h::h2::t2)(h:=h)(t:=h2::t2)(h2:=h2)(t2:=t2).
  reflexivity. apply H. reflexivity.
Qed.

Theorem snoc_app: forall X (l:list X) (x:X),  snoc l x = l ++ [x].
Proof.
  intros.
  induction l as [|h t].
  reflexivity.
  simpl. apply f_equal. apply IHt.
Qed.

Theorem app_nil2: forall X (l1:list X), l1 ++ [] = l1.
Proof.
  induction l1.
  reflexivity.
  simpl. apply f_equal. apply IHl1.
Qed.

Theorem list_app_same: forall X (l1 l2 n: list X),  l1 ++ n = l2 ++ n -> l1 = l2.
Proof.
admit.

Theorem S_greater: forall n:nat , blt_nat n (S n) = true.
Proof.
  intros.
  induction n as [| n']. reflexivity.
  simpl. apply IHn'.
Qed.

Theorem S_plus_greater: forall n m: nat, blt_nat n (S n + m) = true.
Proof.
  intros.
  induction n as [| n'].
  simpl. reflexivity.
  unfold blt_nat. simpl.
  unfold blt_nat in IHn'. apply IHn'.
Qed.

Theorem blt_nat_refl : forall n: nat, blt_nat n n = false.
Proof.
  intros.
  induction n as [| n']. reflexivity.
  unfold blt_nat. unfold blt_nat in IHn'.
  simpl. apply IHn'.
Qed.

Theorem length_app: forall X (l1 l2 : list X), length (l1 ++ l2) = length l1 + (length l2).
Proof.
  intros.
  induction l1 as [| h t].
  Case "l1 = []". simpl. reflexivity.
  Case "l1 = h :: t". simpl. rewrite IHt. reflexivity.
Qed.

Theorem length_contradiction: forall X (x:X) (l1 l2: list X),
    x :: l1 ++ l2 = l2 -> False.
Proof.
  intros.
  destruct l2 as [| h t] eqn:dl.
  inversion H.
  assert (length l2 = length (x :: l1 ++ l2)).
    rewrite dl. rewrite H. reflexivity.
    simpl in H0. rewrite length_app in H0.
    rewrite -> plus_n_Sm in H0. rewrite plus_comm in H0.
  assert (blt_nat (length l2) (S (length l2) + length l1) = false). rewrite <- H0. apply blt_nat_refl.
  assert (blt_nat (length l2) (S (length l2) + length l1) = true). apply S_plus_greater.
  rewrite H1 in H2. inversion H2.
Qed.

Theorem app_same :  forall X (l1 l2 n: list X),  l1 ++ n = l2 ++ n -> l1 = l2.
Proof.
  intros.
  generalize dependent l2.
  induction l1 as [| h t].
  Case "l1 = []".
    intros.
    destruct l2 as [| h2 t2].
    reflexivity.
    simpl in H. symmetry in H. apply length_contradiction in H. inversion H.
  Case "l1 = h :: t".
    intros.
    destruct l2 as [| h2 t2].
    simpl in H. apply length_contradiction in H. inversion H.
    inversion H. apply f_equal.
    apply IHt. apply H2.
Qed.

Theorem rev_tail_init : forall X (l: list X),
    l = rev l -> (init (tail l)) = rev (init (tail l)).
Proof.
  intros.
  destruct l as [ |h1 t1] eqn:dl.
  reflexivity.
  simpl.
  assert (last l<> None). apply last_non_nil with (h:=h1)(t:=t1). apply dl.
  destruct (last l) eqn:lastl.
  assert (l = init l  ++ [x]). apply init_tial. apply lastl.
  assert (h1 = x). apply rev_last with (l:=h1::t1) (t:=t1). reflexivity. apply H. rewrite dl in lastl. apply lastl.
  destruct t1 as [|th tt] eqn:dt1.
  reflexivity.
  assert (t1 = init t1 ++ [x]). apply init_tial.
    apply rev_trans with (l:=l)(h:=h1)(h2:=th)(t2:=tt).
    rewrite <- dt1 in dl. apply dl. apply lastl. apply dt1.
  rewrite <- dt1 in H. rewrite H3 in H.
  rewrite H2 in H.
  inversion H.
  rewrite <- dt1.
  rewrite snoc_app in H5. rewrite <- (snoc_app X (init t1) (x)) in H5.
  rewrite -> rev_snoc in H5. simpl in H5. rewrite snoc_app in H5.
  inversion H5.
  apply app_same with (n:=[x]).
  apply H6.
  unfold not in H0. assert False. apply H0. reflexivity. inversion H1.
Qed.


Theorem rev_destruct: forall X (l:list X) (x: X),
    l = rev l -> last l = Some x -> l = [x] \/ l = x :: snoc (init (tail l)) x.
Proof.
  intros.
  destruct l as [|h t] eqn:dl.
  Case "l = []". inversion H0.
  Case "l = h :: t".
    destruct t as [| h2 t2] eqn:dt.
    SCase "l = [h]". inversion H0. left. reflexivity.
    SCase "l = h :: h2 :: t2". right.
      assert (h = x). apply rev_last with (l:=l)(h:=h)(t:=h2::t2).
        apply dl. rewrite <- dl in H. apply H. rewrite <- dl in H0. apply H0.
      rewrite H1. apply f_equal.
      unfold tail.
      rewrite snoc_app.
      assert (last t = Some x). apply rev_trans with (l:=h::t) (h:=h) (t:=t) (x:=x) (h2:=h2)(t2:=t2).
        reflexivity. rewrite <- dt in H0. apply H0. apply dt.
      assert (t = init t ++ [x]). apply init_tial. apply H2.
      rewrite <- dt. apply H3.
Qed.

Theorem ble_nat_S : forall (n m :nat), ble_nat n m = true -> ble_nat n (S m) = true.
Proof.
  intros n.
  induction n as [| n'].
  intros. reflexivity.
  intros. destruct m as [|m']. inversion H.
    simpl. simpl in H. apply IHn'. apply H.
Qed.

Theorem rev_pal_length : forall X (n: nat) (l: list X), ble_nat (length l) n = true -> l = rev l -> pal l.
Proof.
  intros X n.
  induction n as [| n'].
  Case "length l = 0". intros. destruct l. apply pal_nil. inversion H.
  Case "length l = S n'".
    destruct n' as [| n''] eqn:dn.
    SCase "length l = 1". intros. destruct l eqn:dl.
      SSCase "l = []". apply pal_nil.
      SSCase "l = x :: l0". simpl in H. destruct l0. apply pal_singleton. inversion H.
    SCase "length l = S (S n'')".
      intros.
      destruct l eqn:dl.
      SSCase "l = []". apply pal_nil.
      SSCase "l = x :: l0".
        assert (last l <> None). apply last_non_nil with (h:=x) (t:=l0). apply dl.
        destruct (last l) eqn:lastl.
        SSSCase "last l = Some x0".
          assert (l = [x0] \/ l = x0 :: snoc (init (tail l)) x0). apply rev_destruct.
            rewrite <- dl in H0. apply H0. apply lastl .
          destruct H2.
          SSSSCase "l = [x]". rewrite <- dl. rewrite H2. apply pal_singleton.
          SSSSCase "l = x ...".
            assert (x = x0). apply rev_last with (l:=l)(h:=x)(t:=l0).
              apply dl. rewrite <- dl in H0. apply H0. apply lastl.
            assert (ble_nat (length (init (tail l ))) (S n'') = true).
              rewrite <- dl in H. rewrite H2 in H. simpl in H.
              rewrite length_snoc' with (n:= length (init (tail l))) in H. simpl in H.
              apply ble_nat_S. apply H. reflexivity.
            assert (init (tail l ) = rev (init (tail l ))).
              apply rev_tail_init. rewrite <- dl in H0. apply H0.
            assert (pal (init (tail l))).
              apply IHn'. apply H4. apply H5.
            rewrite <- dl. rewrite H2.
            apply (pal_cc x0 (init (tail l)) H6).
       SSSCase "last l = None". unfold not in H1. assert False. apply H1. reflexivity. inversion H2.
Qed.

Theorem ble_nat_refl :forall n:nat, ble_nat n n  = true.
Proof.
  intros.
  induction n as [| n'].
  reflexivity.
  simpl. apply IHn'.
Qed.

Theorem rev_pal:  forall X (l: list X), l = rev l -> pal l.
Proof.
  intros.
  apply rev_pal_length with (n:= length l).
  apply ble_nat_refl. apply H.
Qed.