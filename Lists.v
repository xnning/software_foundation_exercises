Require Export Induction.

Module NatList.

(* Pairs of Numbers *)

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

Check (pair 3 5).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Eval compute in (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Eval compute in (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall(n m:nat),
    (n, m) = (fst (n, m), snd (n, m)).
Proof.
  reflexivity. Qed.

Theorem surjective_pairing_stuck : forall(p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Abort.

Theorem surjective_pairing : forall(p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

(* Exercise: 1 star (snd_fst_is_swap) *)

Theorem snd_fst_is_swap : forall(p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

(* Exercise: 1 star, optional (fst_swap_is_snd) *)


Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

(* Lists of Numbers *)

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l: natlist) :nat :=
  match l with
  | nil => 0
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2: natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

(* Exercise: 2 stars (list_funs) *)

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | O :: t => nonzeros t
  | x :: t => x :: (nonzeros t)
  end.

Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  simpl. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | x :: t =>
    match evenb x with
      | true  => oddmembers t
      | false => x::(oddmembers t)
    end
  end.

Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
  simpl. reflexivity. Qed.

Fixpoint countoddmembers (l:natlist) : nat :=
  match l with
  | nil => 0
  | x :: t =>
    match evenb x with
      | true  => countoddmembers t
      | false => 1 + (countoddmembers t)
    end
  end.

Example test_countoddmembers1: countoddmembers [1;0;3;1;4;5] = 4.
  simpl. reflexivity. Qed.

Example test_countoddmembers2: countoddmembers [0;2;4] = 0.
  simpl. reflexivity. Qed.

Example test_countoddmembers3: countoddmembers nil = 0.
  simpl. reflexivity. Qed.

(* Exercise: 3 stars, advanced (alternate) *)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h1::t1 => match l2 with
             | nil => l1
             | h2::t2 => h1 :: h2 :: (alternate t1 t2)
             end
  end.

Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  simpl. reflexivity. Qed.
Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
  simpl. reflexivity. Qed.
Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
  simpl. reflexivity. Qed.
Example test_alternate4: alternate [] [20;30] = [20;30].
  simpl. reflexivity. Qed.

Definition bag := natlist.

(* Exercise: 3 stars (bag_functions) *)

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | h :: t => match beq_nat h v with
             | true => 1 + (count v t)
             | false => count v t
             end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
  simpl. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
  simpl. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
  simpl. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag := v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
  simpl. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
  simpl. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool := blt_nat 0 (count v s).

Example test_member1: member 1 [1;4;1] = true.
  simpl. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
  simpl. reflexivity. Qed.

(* Exercise: 3 stars, optional (bag_more_functions) *)

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => match beq_nat v h with
             | true => t
             | false => h :: (remove_one v t)
             end
  end.

Example test_remove_one1: count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  simpl. reflexivity. Qed.
Example test_remove_one2: count 5 (remove_one 5 [2;1;4;1]) = 0.
  simpl. reflexivity. Qed.
Example test_remove_one3: count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  simpl. reflexivity. Qed.
Example test_remove_one4: count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  simpl. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => match beq_nat v h with
             | true => remove_all v t
             | false => h :: (remove_all v t)
             end
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
  simpl. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
  simpl. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
  simpl. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
  simpl. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
  | nil => true
  | h :: t => match member h s2 with
             | true => subset t (remove_one h s2)
             | false => false
             end
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
  simpl. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
  simpl. reflexivity. Qed.

(* Exercise: 3 stars (bag_theorem) *)
Theorem list_add_count : forall n:nat, forall l:bag,
    count n (add n l) = count n l + 1.
Proof.
  intros n l.
  destruct l as [ | h t].
  Case "l = []".
    simpl.
    rewrite <- beq_nat_refl.
    reflexivity.
  Case "l = h :: t".
    simpl.
    rewrite <- beq_nat_refl.
    rewrite <- plus_1_l.
    rewrite -> plus_comm.
    reflexivity.
Qed.

(* Reasoning About Lists *)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n l'".
    reflexivity. Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons n l1'".
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons".
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Fixpoint snoc (l:natlist) (v:nat) : natlist :=
  match l with
  | nil => [v]
  | h :: t => h :: (snoc t v)
  end.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => snoc (rev t) h
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = []".
    reflexivity.
  Case "l = n :: l'".
    simpl.
    rewrite <- IHl'.
Abort.

Theorem length_snoc : forall n : nat, forall l : natlist,
  length (snoc l n) = S (length l).
Proof.
  intros n l. induction l as [| n' l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n' l'".
    simpl. rewrite -> IHl'. reflexivity. Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> length_snoc.
    rewrite -> IHl'. reflexivity. Qed.

(*  SearchAbout rev. *)

(* Exercise: 3 stars (list_exercises) *)

Theorem app_nil_end : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l.
  induction l as [ | h t].
  Case "l = []".
    reflexivity.
  Case "l = h :: t".
    simpl.
    rewrite -> IHt.
    reflexivity.
Qed.

Theorem rev_snoc : forall l: natlist, forall n: nat, rev (snoc l n) = n :: (rev l).
Proof.
  intros l n.
  induction l as [ | h t].
  Case "l = []".
    simpl. reflexivity.
  Case "l = h :: t".
    simpl.
    rewrite -> IHt.
    simpl. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l.
  induction l as [| h t].
  Case "l = []".
    simpl. reflexivity.
  Case "l = h :: t".
    simpl.
    rewrite -> rev_snoc.
    rewrite -> IHt.
    reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  induction l1 as [|h t].
  Case "l1 = []".
    simpl.
    rewrite -> app_assoc.
    reflexivity.
  Case "l1 = h :: t".
    simpl.
    rewrite -> IHt.
    reflexivity.
Qed.

Theorem snoc_append : forall(l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  intros l n.
  induction l as [ | h t].
  Case "l = []".
    simpl. reflexivity.
  Case "l = h :: t".
  simpl.
  rewrite -> IHt.
  reflexivity.
Qed.

Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros l1 l2.
  induction l1 as [| h t].
  Case "l1 = []".
    simpl.
    rewrite -> app_nil_end.
    reflexivity.
  Case "l1 = h :: t".
    simpl.
    rewrite -> snoc_append.
    rewrite -> snoc_append.
    rewrite -> IHt.
    rewrite -> app_assoc.
    reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1 as [| h t].
  Case "l1 = nil".
    simpl. reflexivity.
  Case "l1 = h :: t".
    destruct h as [ | h'].
    SCase "h = 0".
      simpl.
      rewrite -> IHt.
      reflexivity.
    SCase "h = S h'".
      simpl.
      rewrite -> IHt.
      reflexivity.
Qed.

(* Exercise: 2 stars (beq_natlist) *)

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1 with
  | nil => match l2 with
          | nil => true
          | _ => false
          end
  | h1 :: t1 => match l2 with
               | nil => false
               | h2 :: t2 => andb (beq_nat h1 h2) (beq_natlist t1 t2)
               end
  end.

Example test_beq_natlist1 : (beq_natlist nil nil = true).
  reflexivity. Qed.
Example test_beq_natlist2 : beq_natlist [1;2;3] [1;2;3] = true.
  reflexivity. Qed.
Example test_beq_natlist3 : beq_natlist [1;2;3] [1;2;4] = false.
  reflexivity. Qed.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  intros l.
  induction l as [ | h t].
  Case "l = []".
    simpl. reflexivity.
  Case "l = h :: t".
    simpl.
    rewrite <- beq_nat_refl.
    rewrite <- IHt.
    simpl.
    reflexivity.
Qed.

(* Exercise: 2 stars (list_design) *)

Theorem cons_snoc_app : forall n:nat, forall l1 l2:natlist,
      l1 ++ (n :: l2) = (snoc l1 n) ++ l2.
Proof.
  intros n l1 l2.
  induction l1 as [ | h t].
  Case "l1 = []".
    simpl. reflexivity.
  Case "l1 = h :: t".
    simpl.
    rewrite -> IHt.
    reflexivity.
Qed.

(* Exercise: 3 stars, advanced (bag_proofs) *)

Theorem count_member_nonzero : forall(s : bag),
  ble_nat 1 (count 1 (1 :: s)) = true.
Proof.
  simpl. reflexivity. Qed.

Theorem ble_n_Sn : forall n,
  ble_nat n (S n) = true.
Proof.
  intros n. induction n as [| n'].
  Case "0".
    simpl. reflexivity.
  Case "S n'".
    simpl. rewrite IHn'. reflexivity. Qed.

Theorem remove_decreases_count: forall(s : bag),
  ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros s.
  induction s as [| h t].
  Case "s = nil".
    simpl. reflexivity.
  Case "s = h :: t".
    destruct h as [ | h'].
    SCase "h = 0".
      simpl.
      rewrite -> ble_n_Sn.
      reflexivity.
    SCase "h = S h'".
      simpl.
      rewrite -> IHt.
      reflexivity.
Qed.

(* Exercise: 3 stars, optional (bag_count_sum) *)
Theorem bag_count_sum : forall n:nat, forall s1 s2:bag,
    count n s1 + (count n s2) = count n (sum s1 s2).
Proof.
  intros n s1 s2.
  induction s1 as [| h t].
  Case "s1 = []".
    simpl. reflexivity.
    simpl.
    destruct (beq_nat h n).
    SCase "h = n".
      rewrite <- IHt.
      rewrite -> plus_comm.
      rewrite <- plus_n_Sm.
      rewrite -> plus_comm.
      reflexivity.
    SCase "h /= n".
      rewrite -> IHt. reflexivity.
Qed.

(* Exercise: 4 stars, advanced (rev_injective) *)

Theorem rev_injective : forall(l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 h.
  rewrite <- rev_involutive.
  rewrite <- h.
  rewrite -> rev_involutive.
  reflexivity.
Qed.
