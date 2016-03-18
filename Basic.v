
Inductive day : Type :=
| monday: day
| tuesday: day
| wednesday:day
| thursday:day
.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => monday
               end.

Eval compute in (next_weekday monday).

Example test_next_weekday: (next_weekday monday) = tuesday.

Proof. simpl. reflexivity. Qed.

Inductive bool: Type :=
| true: bool
| false :bool.

Definition negb (b:bool):bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb: (orb true false) = true.
Proof. reflexivity. Qed.

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | false => true
  | true => negb b2
  end.

Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  andb (andb b1 b2) b3.

Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

Check true.
Check negb.

Module Playground1.

  Inductive nat : Type :=
  | O: nat
  | S: nat -> nat.
  
  Definition pred (n:nat) :nat :=
    match n with 
    | O => O
    | S n' => n'
    end.
  End Playground1.

Definition minustwo (n:nat) :nat :=
  match n with
  | O => O
  | S O => O
  | S (S n) => n
  end.

Check S (S (S (S O))).
  
Eval compute in (minustwo 4).

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: (oddb (S O)) = true.
Proof. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. reflexivity. Qed.

Module Playground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Eval compute in  (plus (S (S (S O))) (S (S O))).

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. reflexivity. Qed.

Fixpoint minus (n m :nat) :nat :=
  match n, m with
  | O, _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.

End Playground2.

Fixpoint exp (base power: nat): nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

Fixpoint factorial (n:nat) : nat := 
  match n with
  | O => 1
  | S n => mult (S n) (factorial n)
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

Notation "x + y" := (plus x y) 
                       (at level 50, left associativity) 
                       : nat_scope.
Notation "x - y" := (minus x y) 
                       (at level 50, left associativity) 
                       : nat_scope.
Notation "x × y" := (mult x y) 
                       (at level 40, left associativity) 
                       : nat_scope.

Check ((0 + 1) + 1).

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. reflexivity. Qed.

(* exercise 2 *)
Definition blt_nat (n m : nat) : bool :=
  andb (ble_nat n m) (negb (beq_nat n m)).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.

Theorem plus_O_n : forall n :nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_n_O : forall n:nat, n + 0 = n.
Proof.
  intros n. simpl. Abort.

Theorem plus_1_l : forall n:nat , 1+ n =S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.

(* Proof by simplification *)

Theorem plus_id_example : forall n m:nat,
  n = m -> 
  n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity. Qed.

(* exercise 1 *)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros Hmn.
  intros Hmo.
  rewrite -> Hmn.
  rewrite <- Hmo.
  reflexivity.
  Qed.


Theorem mult_0_plus : forall n m : nat,
  (0 + n) × m = n × m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity. Qed.

(* exercise 2 *)

Theorem mult_S_1 : forall n m : nat,
  m = S n -> 
  m × (1 + n) = m × m.
Proof.
  intros n m.
  intros H.
  rewrite -> (plus_1_l n).
  rewrite <- H.
  reflexivity.
  Qed.

(* proof by case analysis *)

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [ | n'].
  reflexivity.
  reflexivity. Qed.
  
Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
    reflexivity.
    reflexivity. Qed.

(* Exercise: 1 star (zero_nbeq_plus_1) *)

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n.
  destruct n as [ | n'].
  reflexivity.
  reflexivity. Qed.

(* Exercise: 2 stars (boolean_functions) *)


Theorem identity_fn_applied_twice : 
  forall(f : bool -> bool), 
  (forall(x : bool), f x = x) ->
  forall(b : bool), f (f b) = b.
Proof.
  intros f.
  intros id.
  intros b.
  rewrite -> (id b).
  rewrite -> (id b).
  reflexivity. Qed.

(* Exercise: 2 stars (andb_eq_orb) *)

Theorem andb_false :  forall n:bool,
    andb false n = false.
Proof.
  intros n.
  reflexivity. Qed.

Theorem orb_true : forall n:bool,
    orb true n = true.
Proof.
  intros n.
  reflexivity. Qed.

Theorem andb_eq_orb : 
  forall(b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  intros H.
  destruct b.
  rewrite <- (orb_true c).
  rewrite <- H.
  reflexivity.
  rewrite <- (andb_false c).
  rewrite -> H.
  reflexivity.
  Qed.
  
(* Exercise: 3 stars (binary) *)

  Inductive bin : Type :=
  | Z : bin
  | T : bin -> bin
  | MT : bin -> bin.

  Fixpoint incr (b:bin) :bin :=
    match b with
    | Z => MT Z
    | T n => MT n
    | MT n => T (incr n)
    end.


  Fixpoint bin_to_nat (b:bin) :nat :=
    match b with
    | Z => 0
    | T n => 2 * (bin_to_nat n)
    | MT n => 2 * (bin_to_nat n) + 1
    end.

  (* Exercise: 2 stars, optional (decreasing) *)
  
  Fixpoint rec (m:nat) (n:nat) :nat :=
    match S m, S n with
    | O, _ => O
    | _, O => O
    | S m', S n' => rec n' m'
    end.
  
          
              
  
  

  

  
