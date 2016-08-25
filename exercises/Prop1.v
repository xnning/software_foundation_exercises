(** * Prop: Propositions and Evidence *)

Require Export Logic.

(* ####################################################### *)
(** * Inductively Defined Propositions *)

(** In chapter [Basics] we defined a _function_ [evenb] that tests a
    number for evenness, yielding [true] if so.  We can use this
    function to define the _proposition_ that some number [n] is
    even: *)

Definition even (n:nat) : Prop :=
  evenb n = true.

(** That is, we can define "[n] is even" to mean "the function [evenb]
    returns [true] when applied to [n]."

    Note that here we have given a name
    to a proposition using a [Definition], just as we have
    given names to expressions of other sorts. This isn't a fundamentally
    new kind of proposition;  it is still just an equality. *)

(** Another alternative is to define the concept of evenness
    directly.  Instead of going via the [evenb] function ("a number is
    even if a certain computation yields [true]"), we can say what the
    concept of evenness means by giving two different ways of
    presenting _evidence_ that a number is even. *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).


(** The first line declares that [ev] is a proposition -- or,
    more formally, a family of propositions "indexed by" natural
    numbers.  (That is, for each number [n], the claim that "[n] is
    even" is a proposition.)  Such a family of propositions is
    often called a _property_ of numbers.

    The last two lines declare the two ways to give evidence that a
    number [m] is even.  First, [0] is even, and [ev_0] is evidence
    for this.  Second, if [m = S (S n)] for some [n] and we can give
    evidence [e] that [n] is even, then [m] is also even, and [ev_SS n
    e] is the evidence.
*)


(** **** Exercise: 1 star (double_even)  *)

Theorem double_even : forall n,
  ev (double n).
Proof.
  induction n as [| n'].
  simpl. apply ev_0.
  simpl. apply (ev_SS (double n') IHn').
Qed.
(** [] *)



(* ##################################################### *)

(** For [ev], we had already defined [even] as a function (returning a
   boolean), and then defined an inductive relation that agreed with
   it. However, we don't necessarily need to think about propositions
   first as boolean functions, we can start off with the inductive
   definition.
*)

(** As another example of an inductively defined proposition, let's
    define a simple property of natural numbers -- we'll call it
    "[beautiful]." *)

(** Informally, a number is [beautiful] if it is [0], [3], [5], or the
    sum of two [beautiful] numbers.

    More pedantically, we can define [beautiful] numbers by giving four
    rules:

       - Rule [b_0]: The number [0] is [beautiful].
       - Rule [b_3]: The number [3] is [beautiful].
       - Rule [b_5]: The number [5] is [beautiful].
       - Rule [b_sum]: If [n] and [m] are both [beautiful], then so is
         their sum. *)

(** We will see many definitions like this one during the rest
    of the course, and for purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation: *)
(**
                              -----------                               (b_0)
                              beautiful 0

                              ------------                              (b_3)
                              beautiful 3

                              ------------                              (b_5)
                              beautiful 5

                       beautiful n     beautiful m
                       ---------------------------                      (b_sum)
                              beautiful (n+m)
*)

(** *** *)
(** Each of the textual rules above is reformatted here as an
    inference rule; the intended reading is that, if the _premises_
    above the line all hold, then the _conclusion_ below the line
    follows.  For example, the rule [b_sum] says that, if [n] and [m]
    are both [beautiful] numbers, then it follows that [n+m] is
    [beautiful] too.  If a rule has no premises above the line, then
    its conclusion holds unconditionally.

    These rules _define_ the property [beautiful].  That is, if we
    want to convince someone that some particular number is [beautiful],
    our argument must be based on these rules.  For a simple example,
    suppose we claim that the number [5] is [beautiful].  To support
    this claim, we just need to point out that rule [b_5] says so.
    Or, if we want to claim that [8] is [beautiful], we can support our
    claim by first observing that [3] and [5] are both [beautiful] (by
    rules [b_3] and [b_5]) and then pointing out that their sum, [8],
    is therefore [beautiful] by rule [b_sum].  This argument can be
    expressed graphically with the following _proof tree_: *)
(**
         ----------- (b_3)   ----------- (b_5)
         beautiful 3         beautiful 5
         ------------------------------- (b_sum)
                   beautiful 8
*)
(** *** *)
(**
    Of course, there are other ways of using these rules to argue that
    [8] is [beautiful], for instance:
         ----------- (b_5)   ----------- (b_3)
         beautiful 5         beautiful 3
         ------------------------------- (b_sum)
                   beautiful 8
*)

(** **** Exercise: 1 star (varieties_of_beauty)  *)
(** How many different ways are there to show that [8] is [beautiful]? *)

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *)
(** ** Constructing Evidence *)

(** In Coq, we can express the definition of [beautiful] as
    follows: *)

Inductive beautiful : nat -> Prop :=
  b_0   : beautiful 0
| b_3   : beautiful 3
| b_5   : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).

(** *** *)
(**
    The rules introduced this way have the same status as proven
    theorems; that is, they are true axiomatically.
    So we can use Coq's [apply] tactic with the rule names to prove
    that particular numbers are [beautiful].  *)

Theorem three_is_beautiful: beautiful 3.
Proof.
   (* This simply follows from the rule [b_3]. *)
   apply b_3.
Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
   (* First we use the rule [b_sum], telling Coq how to
      instantiate [n] and [m]. *)
   apply b_sum with (n:=3) (m:=5).
   (* To solve the subgoals generated by [b_sum], we must provide
      evidence of [beautiful 3] and [beautiful 5]. Fortunately we
      have rules for both. *)
   apply b_3.
   apply b_5.
Qed.

(** *** *)
(** As you would expect, we can also prove theorems that have
hypotheses about [beautiful]. *)

Theorem beautiful_plus_eight: forall n, beautiful n -> beautiful (8+n).
Proof.
  intros n B.
  apply b_sum with (n:=8) (m:=n).
  apply eight_is_beautiful.
  apply B.
Qed.

(** **** Exercise: 2 stars (b_times2)  *)
Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
Proof.
  intros n B.
  simpl.
  apply b_sum with (n:=n) (m:=n+0).
  apply B. apply b_sum with (n:=n) (m:=0). apply B. apply b_0.
Qed.
(** [] *)

(** **** Exercise: 3 stars (b_timesm)  *)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
  intros n m B.
  induction m as [| m'].
  simpl. apply b_0.
  simpl. apply b_sum. apply B. apply IHm'.
Qed.
(** [] *)


(* ####################################################### *)
(** * Using Evidence in Proofs *)
(** ** Induction over Evidence *)

(** Besides _constructing_ evidence that numbers are beautiful, we can
    also _reason about_ such evidence. *)

(** The fact that we introduced [beautiful] with an [Inductive]
    declaration tells Coq not only that the constructors [b_0], [b_3],
    [b_5] and [b_sum] are ways to build evidence, but also that these
    four constructors are the _only_ ways to build evidence that
    numbers are beautiful. *)

(** In other words, if someone gives us evidence [E] for the assertion
    [beautiful n], then we know that [E] must have one of four shapes:

      - [E] is [b_0] (and [n] is [O]),
      - [E] is [b_3] (and [n] is [3]),
      - [E] is [b_5] (and [n] is [5]), or
      - [E] is [b_sum n1 n2 E1 E2] (and [n] is [n1+n2], where [E1] is
        evidence that [n1] is beautiful and [E2] is evidence that [n2]
        is beautiful). *)

(** *** *)
(** This permits us to _analyze_ any hypothesis of the form [beautiful
    n] to see how it was constructed, using the tactics we already
    know.  In particular, we can use the [induction] tactic that we
    have already seen for reasoning about inductively defined _data_
    to reason about inductively defined _evidence_.

    To illustrate this, let's define another property of numbers: *)

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

(** **** Exercise: 1 star (gorgeous_tree)  *)
(** Write out the definition of [gorgeous] numbers using inference rule
    notation.

(* FILL IN HERE *)
[]
*)


(** **** Exercise: 1 star (gorgeous_plus13)  *)
Theorem gorgeous_plus13: forall n,
  gorgeous n -> gorgeous (13+n).
Proof.
  intros n H.
  apply g_plus3. apply g_plus5. apply g_plus5. apply H.
Qed.
(** [] *)

(** *** *)
(** It seems intuitively obvious that, although [gorgeous] and
    [beautiful] are presented using slightly different rules, they are
    actually the same property in the sense that they are true of the
    same numbers.  Indeed, we can prove this. *)


Theorem gorgeous__beautiful_FAILED : forall n,
  gorgeous n -> beautiful n.
Proof.
   intros. induction n as [| n'].
   Case "n = 0". apply b_0.
   Case "n = S n'". (* We are stuck! *)
Abort.

(** The problem here is that doing induction on [n] doesn't yield a
    useful induction hypothesis. Knowing how the property we are
    interested in behaves on the predecessor of [n] doesn't help us
    prove that it holds for [n]. Instead, we would like to be able to
    have induction hypotheses that mention other numbers, such as [n -
    3] and [n - 5]. This is given precisely by the shape of the
    constructors for [gorgeous]. *)


(** *** *)

(** Let's see what happens if we try to prove this by induction on the evidence [H]
   instead of on [n]. *)

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


(* These exercises also require the use of induction on the evidence. *)

(** **** Exercise: 2 stars (gorgeous_sum)  *)
Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  intros.
  induction H as [|n'|n'].
  apply H0.
  rewrite <- plus_assoc. apply g_plus3. apply IHgorgeous.
  rewrite <- plus_assoc. apply g_plus5. apply IHgorgeous.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (beautiful__gorgeous)  *)
Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
  intros.
  induction H as [| | | n1 n2].
  Case "n = 0". apply g_0.
  Case "n = 3". apply g_plus3. apply g_0.
  Case "n = 5". apply g_plus5. apply g_0.
  Case "n = n1 + n2". apply gorgeous_sum. apply IHbeautiful1. apply IHbeautiful2.
Qed.
(** [] *)




(** **** Exercise: 3 stars, optional (g_times2)  *)
(** Prove the [g_times2] theorem below without using [gorgeous__beautiful].
    You might find the following helper lemma useful. *)

Lemma helper_g_times2 : forall x y z, x + (z + y) = z + x + y.
Proof.
  intros.
  rewrite -> plus_assoc.
  rewrite -> (plus_comm x z).
  reflexivity.
Qed.

Theorem g_times2: forall n, gorgeous n -> gorgeous (2*n).
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
(** [] *)



(** Here is a proof that the inductive definition of evenness implies
the computational one. *)

Theorem ev__even : forall n,
  ev n -> even n.
Proof.
  intros n E. induction E as [| n' E'].
  Case "E = ev_0".
    unfold even. reflexivity.
  Case "E = ev_SS n' E'".
    unfold even. apply IHE'.
Qed.

(** **** Exercise: 1 star (ev__even)  *)
(** Could this proof also be carried out by induction on [n] instead
    of [E]?  If not, why not? *)

(* FILL IN HERE *)
(** [] *)

(** Intuitively, the induction principle [ev n] evidence [ev n] is
    similar to induction on [n], but restricts our attention to only
    those numbers for which evidence [ev n] could be generated. *)

(** **** Exercise: 1 star (l_fails)  *)
(** The following proof attempt will not succeed.
     Theorem l : forall n,
       ev n.
     Proof.
       intros n. induction n.
         Case "O". simpl. apply ev_0.
         Case "S".
           ...
   Intuitively, we expect the proof to fail because not every
   number is even. However, what exactly causes the proof to fail?

(* FILL IN HERE *)
*)
(** [] *)

(** Here's another exercise requiring induction on evidence. *)
(** **** Exercise: 2 stars (ev_sum)  *)

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
(** [] *)



(* ####################################################### *)
(** ** Inversion on Evidence *)


(** Having evidence for a proposition is useful while proving, because we
   can _look_ at that evidence for more information. For example, consider
    proving that, if [n] is even, then [pred (pred n)] is
    too.  In this case, we don't need to do an inductive proof.  Instead
    the [inversion] tactic provides all of the information that we need.

 *)

Theorem ev_minus2: forall n,  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0.
  Case "E = ev_SS n' E'". simpl. apply E'.  Qed.

(** **** Exercise: 1 star, optional (ev_minus2_n)  *)
(** What happens if we try to use [destruct] on [n] instead of [inversion] on [E]? *)

(* FILL IN HERE *)
(** [] *)

(** *** *)
(** Here is another example, in which [inversion] helps narrow down to
the relevant cases. *)

Theorem SSev__even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  apply E'. Qed.

(** ** The Inversion Tactic Revisited *)

(** These uses of [inversion] may seem a bit mysterious at first.
    Until now, we've only used [inversion] on equality
    propositions, to utilize injectivity of constructors or to
    discriminate between different constructors.  But we see here
    that [inversion] can also be applied to analyzing evidence
    for inductively defined propositions.

    (You might also expect that [destruct] would be a more suitable
    tactic to use here. Indeed, it is possible to use [destruct], but
    it often throws away useful information, and the [eqn:] qualifier
    doesn't help much in this case.)

    Here's how [inversion] works in general.  Suppose the name
    [I] refers to an assumption [P] in the current context, where
    [P] has been defined by an [Inductive] declaration.  Then,
    for each of the constructors of [P], [inversion I] generates
    a subgoal in which [I] has been replaced by the exact,
    specific conditions under which this constructor could have
    been used to prove [P].  Some of these subgoals will be
    self-contradictory; [inversion] throws these away.  The ones
    that are left represent the cases that must be proved to
    establish the original goal.

    In this particular case, the [inversion] analyzed the construction
    [ev (S (S n))], determined that this could only have been
    constructed using [ev_SS], and generated a new subgoal with the
    arguments of that constructor as new hypotheses.  (It also
    produced an auxiliary equality, which happens to be useless here.)
    We'll begin exploring this more general behavior of inversion in
    what follows. *)


(** **** Exercise: 1 star (inversion_practice)  *)
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros.
  inversion H.
  inversion H1.
  apply H3.
Qed.

(** The [inversion] tactic can also be used to derive goals by showing
    the absurdity of a hypothesis. *)

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros.
  inversion H. inversion H1. inversion H3.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (ev_ev__ev)  *)
(** Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m H1 H2.
  induction H2 as[ |n'].
  Case "n = 0". simpl in H1. apply H1.
  Case "n = S (S n')".
    inversion H1. apply IHev in H0. apply H0.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (ev_plus_plus)  *)
(** Here's an exercise that just requires applying existing lemmas.  No
    induction or even case analysis is needed, but some of the rewriting
    may be tedious. *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros.
  assert (ev (n + m + (n + p))). apply ev_sum. apply H. apply H0.
  rewrite plus_swap in H1. rewrite plus_assoc in H1. rewrite plus_assoc in H1.
  rewrite <- double_plus in H1. rewrite <- plus_assoc in H1.
  apply ev_ev__ev with (n:= double n). apply H1. apply double_even.
Qed.
(** [] *)


(* ####################################################### *)
(** * Discussion and Variations *)
(** ** Computational vs. Inductive Definitions *)

(** We have seen that the proposition "[n] is even" can be
    phrased in two different ways -- indirectly, via a boolean testing
    function [evenb], or directly, by inductively describing what
    constitutes evidence for evenness.  These two ways of defining
    evenness are about equally easy to state and work with.  Which we
    choose is basically a question of taste.

    However, for many other properties of interest, the direct
    inductive definition is preferable, since writing a testing
    function may be awkward or even impossible.

    One such property is [beautiful].  This is a perfectly sensible
    definition of a set of numbers, but we cannot translate its
    definition directly into a Coq Fixpoint (or into a recursive
    function in any other common programming language).  We might be
    able to find a clever way of testing this property using a
    [Fixpoint] (indeed, it is not too hard to find one in this case),
    but in general this could require arbitrarily deep thinking.  In
    fact, if the property we are interested in is uncomputable, then
    we cannot define it as a [Fixpoint] no matter how hard we try,
    because Coq requires that all [Fixpoint]s correspond to
    terminating computations.

    On the other hand, writing an inductive definition of what it
    means to give evidence for the property [beautiful] is
    straightforward. *)




(* ####################################################### *)
(** ** Parameterized Data Structures *)

(** So far, we have only looked at propositions about natural numbers. However,
   we can define inductive predicates about any type of data. For example,
   suppose we would like to characterize lists of _even_ length. We can
   do that with the following definition.  *)

Inductive ev_list {X:Type} : list X -> Prop :=
  | el_nil : ev_list []
  | el_cc  : forall x y l, ev_list l -> ev_list (x :: y :: l).

(** Of course, this proposition is equivalent to just saying that the
length of the list is even. *)

Lemma ev_list__ev_length: forall X (l : list X), ev_list l -> ev (length l).
Proof.
    intros X l H. induction H.
    Case "el_nil". simpl. apply ev_0.
    Case "el_cc".  simpl.  apply ev_SS. apply IHev_list.
Qed.

(** However, because evidence for [ev] contains less information than
evidence for [ev_list], the converse direction must be stated very
carefully. *)

Lemma ev_length__ev_list: forall X n, ev n -> forall (l : list X), n = length l -> ev_list l.
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


(** **** Exercise: 4 stars (palindromes)  *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
        c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)

    - Prove [pal_app_rev] that
       forall l, pal (l ++ rev l).
    - Prove [pal_rev] that
       forall l, pal l -> l = rev l.
*)

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
(** [] *)

(* Again, the converse direction is much more difficult, due to the
lack of evidence. *)

(** **** Exercise: 5 stars, optional (palindrome_converse)  *)
(** Using your definition of [pal] from the previous exercise, prove
    that
     forall l, l = rev l -> pal l.
*)

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

Theorem last_trans :forall X (l: list X) (h h2 x: X) (t t2:list X),
    l = h :: t -> last l = Some x -> t = h2 :: t2 -> last t = Some x.
Proof.
  intros.
  rewrite H in H0. rewrite H1 in H0.
  simpl in H0.
  rewrite H1. simpl. apply H0.
Qed.

Theorem destruct_list : forall X (l: list X) (x: X),
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
  apply last_trans with (l:=h::h2::t2)(h:=h)(t:=h2::t2)(h2:=h2)(t2:=t2).
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
  assert (l = init l  ++ [x]). apply destruct_list. apply lastl.
  assert (h1 = x). apply rev_last with (l:=h1::t1) (t:=t1). reflexivity. apply H. rewrite dl in lastl. apply lastl.
  destruct t1 as [|th tt] eqn:dt1.
  reflexivity.
  assert (t1 = init t1 ++ [x]). apply destruct_list.
    apply last_trans with (l:=l)(h:=h1)(h2:=th)(t2:=tt).
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
      assert (last t = Some x). apply last_trans with (l:=h::t) (h:=h) (t:=t) (x:=x) (h2:=h2)(t2:=t2).
        reflexivity. rewrite <- dt in H0. apply H0. apply dt.
      assert (t = init t ++ [x]). apply destruct_list. apply H2.
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
  Case "length l <= 0". intros. destruct l. apply pal_nil. inversion H.
  Case "length l <= S n'".
    destruct n' as [| n''] eqn:dn.
    SCase "length l <= 1". intros. destruct l eqn:dl.
      SSCase "l = []". apply pal_nil.
      SSCase "l = x :: l0". simpl in H. destruct l0. apply pal_singleton. inversion H.
    SCase "length l <= S (S n'')".
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
          SSSSCase "l = x0 :: snoc (init (tail l)) x0".
            assert (ble_nat (length (init (tail l ))) (S n'') = true).
              rewrite <- dl in H. rewrite H2 in H. simpl in H.
              rewrite length_snoc' with (n:= length (init (tail l))) in H. simpl in H.
              apply ble_nat_S. apply H. reflexivity.
            assert (init (tail l) = rev (init (tail l))).
              apply rev_tail_init. rewrite <- dl in H0. apply H0.
            assert (pal (init (tail l))).
              apply IHn'. apply H3. apply H4.
            rewrite <- dl. rewrite H2.
            apply (pal_cc x0 (init (tail l)) H5).
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

(** [] *)



(* ####################################################### *)
(** ** Relations *)

(** A proposition parameterized by a number (such as [ev] or
    [beautiful]) can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module LeModule.


(** One useful example is the "less than or equal to"
    relation on numbers. *)

(** The following definition should be fairly intuitive.  It
    says that there are two ways to give evidence that one number is
    less than or equal to another: either observe that they are the
    same number, or give evidence that the first is less than or equal
    to the predecessor of the second. *)

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).


(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] in chapter [Prop].  We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) -> 2+2=5].) *)

(** *** *)
(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** *** *)
(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

End LeModule.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall n:nat, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 : forall n, ev (S n) -> next_even n (S n)
  | ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

(** **** Exercise: 2 stars (total_relation)  *)
(** Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)

Inductive total_relation: nat -> nat -> Prop :=
  | tr : forall n m:nat, total_relation n m.
(** [] *)

(** **** Exercise: 2 stars (empty_relation)  *)
(** Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

Inductive empty_relation: nat -> nat -> Prop := .
(** [] *)

(** **** Exercise: 2 stars, optional (le_exercises)  *)
(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros.
  induction H0.
  Case "n = o". apply H.
  Case "o = S m0. n <= m0". apply le_S. apply IHle.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  induction n as [| n'].
  apply le_n.
  apply (le_S 0 n' IHn').
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros.
  induction H.
  apply le_n.
  apply le_S. apply IHle.
Qed.


Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros.
  inversion H.
  apply le_n.
  apply le_trans with (m:=n) (n:= S n) (o:=m).
  apply le_S. apply le_n. apply H1.
Qed.


Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros.
  induction b as [| b'].
  rewrite <- plus_n_O. apply le_n.
  rewrite <- plus_n_Sm. apply le_S. apply IHb'.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
 unfold lt.
 intros. split.
 Case "left". apply le_trans with (m:= S n1) (n:=S (n1+n2)).
   apply n_le_m__Sn_le_Sm. apply le_plus_l. apply H.
 Case "right". apply le_trans with (m:= S n2) (n:=S (n1+n2)).
   apply n_le_m__Sn_le_Sm. rewrite plus_comm. apply le_plus_l. apply H.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt.
  intros.
  apply le_S. apply H.
Qed.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m'].
  intros. destruct n. apply le_n. inversion H.
  intros. destruct n. apply O_le_n. apply n_le_m__Sn_le_Sm.
    simpl in H. apply IHm' in H. apply H.
Qed.

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  intros.
  induction H.
  apply ble_nat_refl.
  apply ble_nat_S. apply IHle.
Qed.

Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.
Proof.
  intros.
  apply le_ble_nat.
  apply le_trans with (m:=n)(n:=m)(o:=o).
  apply ble_nat_true. apply H.
  apply ble_nat_true. apply H0.
Qed.

(** **** Exercise: 2 stars, optional (ble_nat_false)  *)
Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  intros.
  unfold not.
  intros.
  apply le_ble_nat in H0. rewrite H in H0. inversion H0.
Qed.
(** [] *)


(** **** Exercise: 3 stars (R_provability2)  *)
Module R.
(** We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

(** - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

[]
*)
Example test_R1: R 1 1 2.
apply c3. apply c2. apply c1. Qed.

(** **** Exercise: 3 stars, optional (R_fact)  *)
(** Relation [R] actually encodes a familiar function.  State and prove two
    theorems that formally connects the relation and the function.
    That is, if [R m n o] is true, what can we say about [m],
    [n], and [o], and vice versa?
*)

Theorem R_sum: forall m n o: nat, R m n o -> m + n = o.
Proof.
  intros.
  induction H.
  reflexivity.
  rewrite plus_Sn_m. rewrite IHR. reflexivity.
  rewrite <- plus_n_Sm. rewrite IHR. reflexivity.
  rewrite plus_Sn_m in IHR. rewrite <- plus_n_Sm in IHR. inversion IHR. reflexivity.
  rewrite plus_comm. apply IHR.
Qed.

Theorem R_sum2: forall o m n:nat, m + n = o -> R m n o.
Proof.
  intros o.
  induction o.
  Case "o = 0".
  intros.
  assert (m=0). destruct m. reflexivity. inversion H.
  assert (n=0). destruct n. reflexivity. rewrite H0 in H. inversion H.
  rewrite H0. rewrite H1. apply c1.
  Case "o = S o'".
  intros.
  destruct m as [|m'].
  simpl in H. rewrite H. apply c3. assert(0+o=o). reflexivity. apply IHo in H0. apply H0.
  rewrite plus_Sn_m in H. inversion H. apply c2. rewrite H1. apply IHo in H1. apply H1.
  Qed.
(** [] *)

End R.

(** **** Exercise: 4 stars, advanced (subsequence)  *)
(** A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,
    [1,2,3]
    is a subsequence of each of the lists
    [1,2,3]
    [1,1,1,2,2,3]
    [1,2,7,3]
    [5,6,1,9,9,2,7,3,8]
    but it is _not_ a subsequence of any of the lists
    [1,2]
    [1,3]
    [5,6,2,1,7,3,8]

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove [subseq_refl] that subsequence is reflexive, that is,
      any list is a subsequence of itself.

    - Prove [subseq_app] that for any lists [l1], [l2], and [l3],
      if [l1] is a subsequence of [l2], then [l1] is also a subsequence
      of [l2 ++ l3].

    - (Optional, harder) Prove [subseq_trans] that subsequence is
      transitive -- that is, if [l1] is a subsequence of [l2] and [l2]
      is a subsequence of [l3], then [l1] is a subsequence of [l3].
      Hint: choose your induction carefully!
*)

Inductive subseq {X:Type} : list X -> list X -> Prop :=
| nil_subseq: forall l:list X, subseq nil l
| ref_subseq: forall (x: X) (l1 l2 : list X), subseq l1 l2 -> subseq (x::l1) (x::l2)
| cons_subseq: forall (x: X) (l1 l2: list X), subseq l1 l2 -> subseq l1 (x::l2).

Theorem subseq_refl: forall {X: Type} (l: list X), subseq l l.
Proof.
  intros.
  induction l.
  apply nil_subseq.
  apply ref_subseq. apply IHl.
Qed.

Theorem subseq_app: forall {X: Type} (l1 l2 l3: list X), subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  intros.
  generalize dependent l1.
  generalize dependent l3.
  induction l2 as [| h t].
  Case "l2 = []".
    intros. inversion H. simpl. apply nil_subseq.
  Case "l2 = h :: t".
    intros. inversion H.
    SCase "h :: t = []". apply nil_subseq.
    SCase "l1 = h :: l0". apply (ref_subseq h l0 (t++l3)). apply IHt. apply H2.
    SCase "subseq l1 t". apply (cons_subseq h l1 (t++l3)). apply IHt. apply H2.
Qed.

Theorem subseq_trans: forall {X: Type} (l1 l2 l3 : list X), subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  intros.
  generalize dependent l1.
  generalize dependent l2.
  induction l3 as [| h t].
  Case "l3 = []".
    intros. inversion H0.  rewrite <- H1 in H. apply H.
  Case "l3 = h :: t".
    intros. inversion H0.
    SCase "l2 = []". rewrite <- H1 in H. inversion H. apply nil_subseq.
    SCase "h = x, l2 = x :: l0".
      inversion H.
      SSCase "l1 = []". apply nil_subseq.
      SSCase "l1 = x0 :: l4, l2 = x0 :: l5".
        rewrite <- H7 in H2.  inversion H2.
        rewrite <- H9. rewrite <- H1.
        apply ref_subseq.
        apply IHt with (l2:= l5). rewrite H10 in H3. apply H3. apply H5.
      SSCase "l2 = x :: l5, subseq l1 l5".
        apply cons_subseq. apply IHt with (l2:=l5).
        rewrite <- H7 in H2. inversion H2. rewrite <- H10. apply H3. apply H5.
    SCase "subseq l2 t".
      apply cons_subseq. apply IHt with (l2:=l2). apply H3. apply H.
Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (R_provability)  *)
(** Suppose we give Coq the following definition:
    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.
    Which of the following propositions are provable?

    - [R 2 [1,0]]
    - [R 1 [1,2,1,0]]
    - [R 6 [3,2,1,0]]
*)
Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.

Example R_test1 : R 2 [1; 0].
apply c2. apply c2. apply c1. Qed.
Example R_test2 : R 1 [1;2;1;0].
apply c3. apply c2. apply c3. apply c3. apply c2. apply c2. apply c2. apply c1. Qed.


(** [] *)


(* ##################################################### *)
(** * Programming with Propositions *)

(** As we have seen, a _proposition_ is a statement expressing a factual claim,
    like "two plus two equals four."  In Coq, propositions are written
    as expressions of type [Prop]. . *)

Check (2 + 2 = 4).
(* ===> 2 + 2 = 4 : Prop *)

Check (ble_nat 3 2 = false).
(* ===> ble_nat 3 2 = false : Prop *)

Check (beautiful 8).
(* ===> beautiful 8 : Prop *)

(** *** *)
(** Both provable and unprovable claims are perfectly good
    propositions.  Simply _being_ a proposition is one thing; being
    _provable_ is something else! *)

Check (2 + 2 = 5).
(* ===> 2 + 2 = 5 : Prop *)

Check (beautiful 4).
(* ===> beautiful 4 : Prop *)

(** Both [2 + 2 = 4] and [2 + 2 = 5] are legal expressions
    of type [Prop]. *)

(** *** *)
(** We've mainly seen one place that propositions can appear in Coq: in
    [Theorem] (and [Lemma] and [Example]) declarations. *)

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** But they can be used in many other ways.  For example, we have also seen that
    we can give a name to a proposition using a [Definition], just as we have
    given names to expressions of other sorts. *)

Definition plus_fact : Prop  :=  2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(** We can later use this name in any situation where a proposition is
    expected -- for example, as the claim in a [Theorem] declaration. *)

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity.  Qed.

(** *** *)
(** We've seen several ways of constructing propositions.

       - We can define a new proposition primitively using [Inductive].

       - Given two expressions [e1] and [e2] of the same type, we can
         form the proposition [e1 = e2], which states that their
         values are equal.

       - We can combine propositions using implication and
         quantification. *)
(** *** *)
(** We have also seen _parameterized propositions_, such as [even] and
    [beautiful]. *)

Check (even 4).
(* ===> even 4 : Prop *)
Check (even 3).
(* ===> even 3 : Prop *)
Check even.
(* ===> even : nat -> Prop *)

(** *** *)
(** The type of [even], i.e., [nat->Prop], can be pronounced in
    three equivalent ways: (1) "[even] is a _function_ from numbers to
    propositions," (2) "[even] is a _family_ of propositions, indexed
    by a number [n]," or (3) "[even] is a _property_ of numbers."  *)

(** Propositions -- including parameterized propositions -- are
    first-class citizens in Coq.  For example, we can define functions
    from numbers to propositions... *)

Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

(** ... and then partially apply them: *)

Definition teen : nat->Prop := between 13 19.

(** We can even pass propositions -- including parameterized
    propositions -- as arguments to functions: *)

Definition true_for_zero (P:nat->Prop) : Prop :=
  P 0.

(** *** *)
(** Here are two more examples of passing parameterized propositions
    as arguments to a function.

    The first function, [true_for_all_numbers], takes a proposition
    [P] as argument and builds the proposition that [P] is true for
    all natural numbers. *)

Definition true_for_all_numbers (P:nat->Prop) : Prop :=
  forall n, P n.

(** The second, [preserved_by_S], takes [P] and builds the proposition
    that, if [P] is true for some natural number [n'], then it is also
    true by the successor of [n'] -- i.e. that [P] is _preserved by
    successor_: *)

Definition preserved_by_S (P:nat->Prop) : Prop :=
  forall n', P n' -> P (S n').

(** *** *)
(** Finally, we can put these ingredients together to define
a proposition stating that induction is valid for natural numbers: *)

Definition natural_number_induction_valid : Prop :=
  forall (P:nat->Prop),
    true_for_zero P ->
    preserved_by_S P ->
    true_for_all_numbers P.





(** **** Exercise: 3 stars (combine_odd_even)  *)
(** Complete the definition of the [combine_odd_even] function
    below. It takes as arguments two properties of numbers [Podd] and
    [Peven]. As its result, it should return a new property [P] such
    that [P n] is equivalent to [Podd n] when [n] is odd, and
    equivalent to [Peven n] otherwise. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun(n: nat) => if oddb n then (Podd n) else (Peven n).

(** To test your definition, see whether you can prove the following
    facts: *)

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros.
  destruct (oddb n) eqn:oddn.
  unfold combine_odd_even. rewrite oddn.
  apply H. reflexivity.
  unfold combine_odd_even. rewrite oddn.
  apply H0. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  intros.
  unfold combine_odd_even in H.
  rewrite H0 in H.
  apply H.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  intros.
  unfold combine_odd_even in H.
  rewrite H0 in H. apply H.
Qed.

(** [] *)

(* ##################################################### *)
(** One more quick digression, for adventurous souls: if we can define
    parameterized propositions using [Definition], then can we also
    define them using [Fixpoint]?  Of course we can!  However, this
    kind of "recursive parameterization" doesn't correspond to
    anything very familiar from everyday mathematics.  The following
    exercise gives a slightly contrived example. *)

(** **** Exercise: 4 stars, optional (true_upto_n__true_everywhere)  *)
(** Define a recursive function
    [true_upto_n__true_everywhere] that makes
    [true_upto_n_example] work. *)

Fixpoint true_upto_n__true_everywhere (n:nat) (f:nat -> Prop) :=
  match n with
  |O => true_for_all_numbers f
  | S n' => f n -> (true_upto_n__true_everywhere n' f)
  end.

Example true_upto_n_example :
    (true_upto_n__true_everywhere 3 (fun n => even n))
  = (even 3 -> even 2 -> even 1 -> forall m : nat, even m).
Proof. reflexivity.  Qed.

(** [] *)