Require Export Lists.

Inductive boollist : Type :=
  | bool_nil : boollist
  | bool_cons : bool -> boollist -> boollist.

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Check nil.
(* ===> nil : forall X : Type, list X *)
Check cons.
(* ===> cons : forall X : Type, X -> list X -> list X *)

Check (cons nat 2 (cons nat 1 (nil nat))).

Set Asymmetric Patterns.

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
  | nil => 0
  | cons h t => S (length X t)
  end.

Example test_length1 :
    length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity. Qed.

Example test_length2 :
    length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity. Qed.

Fixpoint app (X : Type) (l1 l2 : list X)
                : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) :=
  match l with
  | nil => cons X v (nil X)
  | cons h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X:Type) (l:list X) : list X :=
  match l with
  | nil => nil X
  | cons h t => snoc X (rev X t) h
  end.

Example test_rev1 :
    rev nat (cons nat 1 (cons nat 2 (nil nat)))
  = (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity. Qed.

Example test_rev2:
  rev bool (nil bool) = nil bool.
Proof. reflexivity. Qed.

Module MumbleBaz.

(* Exercise: 2 stars (mumble_grumble) *)

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.
Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(* Check d (b a 5). *)
Check d mumble (b a 5).
Check d bool (b a 5).
Check e bool true.
Check e mumble (b c 0).
(* Check e bool (b c 0). *)

(* Exercise: 2 stars (baz_num_elts) *)

Inductive baz : Type :=
   | x : baz -> baz
   | y : baz -> bool -> baz.

(* Zero. Because there will be a loop to form elem of baz.*)

End MumbleBaz.

Fixpoint app' X l1 l2 : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons X h (app' X t l2)
  end.

Check app'.
(* ===> forall X : Type, list X -> list X -> list X *)
Check app.
(* ===> forall X : Type, list X -> list X -> list X *)

Fixpoint length' (X:Type) (l:list X) : nat :=
  match l with
  | nil => 0
  | cons h t => S (length' _ t)
  end.

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).
Definition list123' := cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Arguments nil {X}.
Arguments cons {X} _ _. (* use underscore for argument position that has no name *)
Arguments length {X} l.
Arguments app {X} l1 l2.
Arguments rev {X} l.
Arguments snoc {X} l v.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
Check (length list123'').

Fixpoint length'' {X:Type} (l:list X) : nat :=
  match l with
  | nil => 0
  | cons h t => S (length'' t)
  end.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Definition list123''' := [1; 2; 3].

(* Exercise: 2 stars, optional (poly_exercises) *)

Fixpoint repeat {X : Type} (n : X) (count : nat) : list X :=
  match count with
  | O => nil
  | S p => n :: repeat n p
  end.

Example test_repeat1:
  repeat true 2 = cons true (cons true nil).
  reflexivity. Qed.

Theorem nil_app : forall X:Type, forall l:list X,
  app [] l = l.
Proof.
  reflexivity. Qed.

Theorem rev_snoc : forall X : Type,
                   forall v : X,
                   forall s : list X,
  rev (snoc s v) = v :: (rev s).
Proof.
  intros X v s.
  induction s as [ | h t].
  Case "s = []".
    simpl. reflexivity.
  Case "s = h :: t".
    simpl.
    rewrite -> IHt.
    simpl.
    reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l.
  induction l as [ | h t].
  Case "l = []".
    simpl. reflexivity.
  Case "l = h :: t".
  simpl.
  rewrite -> rev_snoc.
  rewrite -> IHt.
  reflexivity.
Qed.

Theorem snoc_with_append : forall X : Type,
                         forall l1 l2 : list X,
                         forall v : X,
  snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  intros X l1 l2 v.
  induction l1 as [| h t].
  Case "l1 = []".
    simpl. reflexivity.
  Case "l1 = h :: t".
  simpl.
  rewrite -> IHt.
  reflexivity.
Qed.

(* Polymorphic Pairs *)

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation "X × Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X × Y) : X :=
  match p with (x,y) => x end.

Definition snd {X Y : Type} (p : X × Y) : Y :=
  match p with (x,y) => y end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X×Y) :=
  match (lx,ly) with
  | ([],_) => []
  | (_,[]) => []
  | (x::tx, y::ty) => (x,y) :: (combine tx ty)
  end.

(* Exercise: 1 star, optional (combine_checks) *)

Check combine.

Eval compute in (combine [1;2] [false;false;true;true]).

(* Exercise: 2 stars (split) *)

Fixpoint split
           {X Y : Type} (l : list (X×Y))
           : (list X) × (list Y) :=
  match l with
  | nil => (nil, nil)
  | (h1, h2) :: t => match (split t) with
                      (t1, t2) => (h1 :: t1, h2 :: t2)
                    end
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
  reflexivity. Qed.

(* Polymorphic Options *)


Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Arguments Some {X} _.
Arguments None {X}.

Fixpoint index {X : Type} (n : nat)
               (l : list X) : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.

Example test_index1 : index 0 [4;5;6;7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 1 [[1];[2]] = Some [2].
Proof. reflexivity. Qed.
Example test_index3 : index 2 [true] = None.
Proof. reflexivity. Qed.

(* Exercise: 1 star, optional (hd_opt_poly) *)

Definition hd_opt {X : Type} (l : list X) : option X :=
  match l with
  | nil => None
  | h :: t => Some h
  end.

Check @hd_opt.

Example test_hd_opt1 : hd_opt [1;2] = Some 1.
  reflexivity. Qed.
Example test_hd_opt2 : hd_opt [[1];[2]] = Some [1].
  reflexivity. Qed.

(* Functions as Data *)

(* Higher-Order Functions *)

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

Check @doit3times.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

(* Partial Application *)

Check plus.

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

(* Digression: Currying *)

(* Exercise: 2 stars, advanced (currying) *)

Definition prod_curry {X Y Z : Type}
  (f : X × Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X × Y) : Z :=
  f (fst p) (snd p).

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall(X Y Z : Type) (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  reflexivity. Qed.

Theorem curry_uncurry : forall(X Y Z : Type)
                               (f : (X × Y) -> Z) (p : X × Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p.
  destruct p as [x y].
  reflexivity. Qed.

(* Filter *)

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
                        else filter test t
  end.

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

(* Anonymous Functions *)

Example test_anon_fun':
  doit3times (fun n => n × n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2':
    filter (fun l => beq_nat (length l) 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

(* Exercise: 2 stars (filter_even_gt7) *)

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun e => andb (evenb e) (blt_nat 7 e)) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof.
  reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
  reflexivity. Qed.

(* Exercise: 3 stars (partition) *)

Definition partition {X : Type} (test : X -> bool) (l : list X)
                     : list X × list X :=
  (filter test l, filter (fun e => negb (test e)) l).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
  reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
  reflexivity. Qed.

(* Map *)
Fixpoint map {X Y:Type} (f:X->Y) (l:list X)
             : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Example test_map2: map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.

Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

(* Map for options *)

(* Exercise: 3 stars (map_rev) *)

Theorem map_snoc : forall(X Y: Type) (f : X -> Y) (x : list X) (y : X),
    map f (snoc x y) = snoc (map f x) (f y).
Proof.
  intros X Y f x y.
  induction x as [ | h t].
  Case "x = []".
    simpl. reflexivity.
  Case "x = h :: t".
    simpl.
    rewrite -> IHt.
    reflexivity.
Qed.

Theorem map_rev : forall(X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l as [|h t].
  Case "l = []".
    simpl. reflexivity.
  Case "l = h :: t".
    simpl.
    rewrite <- IHt.
    rewrite -> map_snoc.
    reflexivity.
Qed.

(* Exercise: 2 stars (flat_map) *)

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X)
                   : (list Y) :=
  match l with
  | nil => nil
  | h :: t => f h ++ flat_map f t
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

(* Exercise: 2 stars, optional (implicit_args) *)

Fixpoint flat_map_explicit (X Y:Type) (f:X -> list Y) (l:list X)
                   : (list Y) :=
  match l with
  | nil => nil
  | h :: t => f h ++ flat_map_explicit X Y f t
  end.

Fixpoint map_explicit (X Y:Type) (f:X->Y) (l:list X)
             : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map_explicit X Y f t)
  end.

(* Fold *)

Fixpoint fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Check (fold andb).
(* ===> fold andb : list bool -> bool -> bool *)

Example fold_example1 : fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 : fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 : fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

(* Exercise: 1 star, advanced (fold_types_different) *)

Definition elem_nat (e: nat) (l: list nat) : bool :=
  fold (fun x y => if beq_nat x e then true else y) l false.

(* Functions For Constructing Functions *)

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Definition override {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if beq_nat k k' then x else f k'.

Definition fmostlytrue := override (override ftrue 1 false) 3 false.

Example override_example1 : fmostlytrue 0 = true.
Proof. reflexivity. Qed.

Example override_example2 : fmostlytrue 1 = false.
Proof. reflexivity. Qed.

Example override_example3 : fmostlytrue 2 = true.
Proof. reflexivity. Qed.

Example override_example4 : fmostlytrue 3 = false.
Proof. reflexivity. Qed.

(* Exercise: 1 star (override_example) *)

Theorem override_example : forall(b:bool),
  (override (constfun b) 3 true) 2 = b.
Proof.
  reflexivity.
Qed.