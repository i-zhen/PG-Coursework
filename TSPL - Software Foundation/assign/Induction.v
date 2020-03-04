(** * Induction: Proof by Induction *)
 

(** The next line imports all of our definitions from the
    previous chapter. *)

Require Export Basics.

(** For it to work, you need to use [coqc] to compile [Basics.v]
    into [Basics.vo].  This is like making a .class file from a .java
    file, or a .o file from a .c file.
  
    Here are two ways to compile your code:
  
     - CoqIDE:
   
         Open [Basics.v].
         In the "Compile" menu, click on "Compile Buffer".
   
     - Command line:
   
         Run [coqc Basics.v]

    *)

(* ###################################################################### *)
(** * Proof by Induction *)

(** We proved in the last chapter that [0] is a neutral element
    for [+] on the left using a simple argument.  The fact that it is
    also a neutral element on the _right_... *)

Theorem plus_0_r_firsttry : forall n:nat,
  n + 0 = n.

(** ... cannot be proved in the same simple way.  Just applying
  [reflexivity] doesn't work: the [n] in [n + 0] is an arbitrary
  unknown number, so the [match] in the definition of [+] can't be
  simplified.  *)

Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

(** And reasoning by cases using [destruct n] doesn't get us much
   further: the branch of the case analysis where we assume [n = 0]
   goes through, but in the branch where [n = S n'] for some [n'] we
   get stuck in exactly the same way.  We could use [destruct n'] to
   get one step further, but since [n] can be arbitrarily large, if we
   try to keep on like this we'll never be done. *)

Theorem plus_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'].
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl.       (* ...but here we are stuck again *)
Abort.

(** To prove such facts -- indeed, to prove most interesting
    facts about numbers, lists, and other inductively defined sets --
    we need a more powerful reasoning principle: _induction_.

    Recall (from high school) the principle of induction over natural
    numbers: If [P(n)] is some proposition involving a natural number
    [n] and we want to show that [P] holds for _all_ numbers [n], we can
    reason like this:
         - show that [P(O)] holds;
         - show that, for any [n'], if [P(n')] holds, then so does
           [P(S n')];
         - conclude that [P(n)] holds for all [n].

    In Coq, the steps are the same but the order is backwards: we
    begin with the goal of proving [P(n)] for all [n] and break it
    down (by applying the [induction] tactic) into two separate
    subgoals: first showing [P(O)] and then showing [P(n') -> P(S
    n')].  Here's how this works for the theorem we are trying to
    prove at the moment: *)


Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Like [destruct], the [induction] tactic takes an [as...]
    clause that specifies the names of the variables to be introduced
    in the subgoals.  In the first branch, [n] is replaced by [0] and
    the goal becomes [0 + 0 = 0], which follows by simplification.  In
    the second, [n] is replaced by [S n'] and the assumption [n' + 0 =
    n'] is added to the context (with the name [IHn'], i.e., the
    Induction Hypothesis for [n']). Notice that the name for the
    induction hypothesis was explicitly given in the [as...] clause of
    the call to [induction]. The goal in this case becomes [(S n') + 0
    = S n'], which simplifies to [S (n' + 0) = S n'], which in turn
    follows from the induction hypothesis. *)

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.

(** **** Exercise: 2 stars (basic_induction)  *)

(** Prove the following lemmas using induction. You might need
    previously proven results. *)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n'  IHn'].
  - (* n = 0*)
    simpl. reflexivity. 
 - (* n = S n' *)
    simpl.  rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
Proof. 
  intros n m. 
  induction n as [| n' IHn'].
  induction m as [| m'].
  - (* n = 0 m = 0 *)
    simpl. reflexivity.
  - (* n = 0 m = m' *)
    simpl. reflexivity.
  - (* n = S n' m = m *)
    simpl. rewrite -> IHn'. reflexivity. 
Qed.


Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. 
  induction n as [| n' IHn'].
  induction m as [| m'].
  - (* n = 0 m = 0 *)
    simpl. reflexivity.
  - (* n = 0 m = S m' *)
    simpl. rewrite -> plus_0_r. reflexivity.
  - (* n = S n' m = m*)
    simpl.  rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.


Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  induction m as [| m'].
  induction p as [| p'].
  - (*n = 0 m = 0 p= 0*)
     simpl. reflexivity.
  - (*n = 0 m = 0 p= S p'*)
     simpl. reflexivity.
  - (*n = 0 m = S m' p = p*)
     simpl. reflexivity.
  - (*n = S n' m = m p = p*)
     simpl. rewrite -> IHn'. reflexivity. Qed.
(** [] *)

(** **** Exercise: 2 stars (double_plus)  *)

(** Consider the following function, which doubles its argument: *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** Use induction to prove this simple fact about [double]: *)

Lemma double_plus : forall n, double n = n + n .
Proof.  
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn', plus_n_Sm. reflexivity. Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (evenb_S)  *)

(** One inconveninent aspect of our definition of [evenb n] is that it
    may need to perform a recursive call on [n - 2]. This makes proofs
    about [evenb n] harder when done by induction on [n], since we may
    need an induction hypothesis about [n - 2]. The following lemma
    gives a better characterization of [evenb (S n)]: *)

Lemma double_neg : forall n : bool,
  negb (negb n) = n.
Proof.
 intros n. destruct n.
 - simpl. reflexivity.
 - simpl. reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - rewrite -> IHn'. 
    simpl. 
    rewrite -> double_neg.
    reflexivity.
Qed.   
(** [] *)

(** **** Exercise: 1 star (destruct_induction)  *)
(** Briefly explain the difference between the tactics
    [destruct] and [induction].  

(I think destruct is useful if the situation is finite. For example, there are only two
possible value true and false for some theorem. However, many proof need infinite 
possible value. Thus, we should use induction tactic.)

*)
(** [] *)


(* ###################################################################### *)
(** * Proofs Within Proofs *)

(** In Coq, as in informal mathematics, large proofs are very
    often broken into a sequence of theorems, with later proofs
    referring to earlier theorems.  Occasionally, however, a proof
    will need some miscellaneous fact that is too trivial (and of too
    little general interest) to bother giving it its own top-level
    name.  In such cases, it is convenient to be able to simply state
    and prove the needed "sub-theorem" right at the point where it is
    used.  The [assert] tactic allows us to do this.  For example, our
    earlier proof of the [mult_0_plus] theorem referred to a previous
    theorem named [plus_O_n].  We can also use [assert] to state and
    prove [plus_O_n] in-line: *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.  Qed.

(** The [assert] tactic introduces two sub-goals.  The first is
    the assertion itself; by prefixing it with [H:] we name the
    assertion [H].  (Note that we could also name the assertion with
    [as] just as we did above with [destruct] and [induction], i.e.,
    [assert (0 + n = n) as H].  Also note that we mark the proof of
    this assertion with curly braces [{ ... }], both for readability
    and so that, when using Coq interactively, we can see more easily
    when we have finished proving the assertion.)  The second goal is
    the same as the one at the point where we invoke [assert], except
    that, in the context, we have the assumption [H] that [0 + n = n].
    That is, [assert] generates one subgoal where we must prove the
    asserted fact and a second subgoal where we can use the asserted
    fact to make progress on whatever we were trying to prove in the
    first place. *)

(** Actually, [assert] will turn out to be handy in many sorts of
    situations.  For example, suppose we want to prove that [(n + m)
    + (p + q) = (m + n) + (p + q)]. The only difference between the
    two sides of the [=] is that the arguments [m] and [n] to the
    first inner [+] are swapped, so it seems we should be able to
    use the commutativity of addition ([plus_comm]) to rewrite one
    into the other.  However, the [rewrite] tactic is a little stupid
    about _where_ it applies the rewrite.  There are three uses of
    [+] here, and it turns out that doing [rewrite -> plus_comm]
    will affect only the _outer_ one... *)

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)...
     it seems like plus_comm should do the trick! *)
  rewrite -> plus_comm.
  (* Doesn't work...Coq rewrote the wrong plus! *)
Abort.

(** To get [plus_comm] to apply at the point where we want it, we can
    introduce a local lemma stating that [n + m = m + n] (for
    the particular [m] and [n] that we are talking about here), prove
    this lemma using [plus_comm], and then use this lemma to do the
    desired rewrite. *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity.  Qed.

(** **** Exercise: 4 stars (mult_comm)  *)
(** Use [assert] to help prove this theorem.  You shouldn't need to
    use induction. *)

Theorem plus_swap : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. 
  assert (H : n + p = p + n). 
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. 
  rewrite -> plus_comm, plus_assoc.
  reflexivity.
Qed.
   

(** Now prove commutativity of multiplication.  (You will probably
    need to define and prove a separate subsidiary theorem to be used
    in the proof of this one.)  You may find that [plus_swap] comes in
    handy. *)

Theorem mult_S_r : forall m n, m * S n = m + (m * n).
Proof.
  intros m n.
(*In the beginning, I wrote induction n at first and then induction m. 
   That led to I cannot prove it.*)
  induction m as [| m' IHm'].
  induction n as [| n' IHn'].
  - (*0 * 1 = 0 + 0 * 0*)
     reflexivity.
  - (* 0 * S (S n') = 0 + 0 * S n' *)
     reflexivity.
   - (* S (n + m' * S n) = S (m' + (n + m' * n)) *)
     simpl. 
     rewrite ->  IHm', plus_swap. 
     reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  induction m as [| n' IHn'].
  induction n as [| m' IHm'].
 - (*0 * 0 = 0 * 0*)
   reflexivity.
 - (*0 * S m' = S m' * 0*)
    rewrite -> mult_S_r.
   (* 0 + 0 * m' = S m' * 0 *)
    rewrite -> IHm'. 
    simpl.
    reflexivity. 
 - (* S n' * n = n * S n' *)
   simpl.
   rewrite -> IHn'.
   (* n + n * n' = n * S n' *)
   rewrite -> mult_S_r.
   reflexivity.
Qed.

(** [] *)

(* ###################################################################### *)
(** * More Exercises *)

(** **** Exercise: 3 stars, optional (more_exercises)  *)
(** Take a piece of paper.  For each of the following theorems, first
    _think_ about whether (a) it can be proved using only
    simplification and rewriting, (b) it also requires case
    analysis ([destruct]), or (c) it also requires induction.  Write
    down your prediction.  Then fill in the proof.  (There is no need
    to turn in your piece of paper; this is just to encourage you to
    reflect before hacking!) *)

Theorem leb_refl : forall n:nat,
  true = leb n n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. 
    reflexivity.
Qed.
  
Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  intros n.
 -(*Use definition directly*)
  simpl.
  reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros [ ].
  - reflexivity.
  - reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat, 
  leb n m = true -> leb (p + n) (p + m) = true.
Proof.
  intros n m p.
  (* suppose leb n m = true *)
  intros H.
  induction p as [| p' IHp'].
  - simpl. rewrite -> H. reflexivity.
  - simpl. rewrite -> IHp'. reflexivity.
Qed.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
 (* use definition *)
  intros n. simpl. reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n.
  induction n as [| n'].
 - reflexivity.
 - (*S (n' + 0) = S n' *) 
    simpl. rewrite -> plus_n_O. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  (* destruct *)
  intros [] [].
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
Qed.


Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros m n p.
  induction m as [| m' IHm'].
  induction n as [| n' IHn'].
  induction p as [| p' IHp'].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite -> IHm', plus_assoc. reflexivity.
Qed.


Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  induction m as [| m' IHm'].
  induction p as [| p' IHp'].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> mult_plus_distr_r. reflexivity.
Qed.

(** [] *)

(** **** Exercise: 2 stars, optional (beq_nat_refl)  *)
(** Prove the following theorem.  Putting [true] on the left-hand side
    of the equality may seem odd, but this is how the theorem is
    stated in the standard library, so we follow suit.  Since
    rewriting works equally well in either direction, we will have no
    problem using the theorem no matter which way we state it. *)

Theorem beq_nat_refl : forall n : nat, 
  true = beq_nat n n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - (* true = beq_nat 0 0 *)
    reflexivity.
  - (* true = beq_nat n' n' *)
    simpl. 
    rewrite -> IHn'.
    reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (plus_swap')  *)
(** The [replace] tactic allows you to specify a particular subterm to
   rewrite and what you want it rewritten to.  More precisely,
   [replace (t) with (u)] replaces (all copies of) expression [t] in
   the goal by expression [u], and generates [t = u] as an additional
   subgoal. This is often useful when a plain [rewrite] acts on the wrong
   part of the goal.  

   Use the [replace] tactic to do a proof of [plus_swap'], just like
   [plus_swap] but without needing [assert (n + m = m + n)]. 
*)

Theorem plus_swap' : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  (* omit indicating n m p *)
  intros.
  rewrite -> plus_assoc, plus_assoc.
  replace (n + m) with (m + n). reflexivity.
  rewrite -> plus_comm.
  reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars (binary_commute)  *)
(** Recall the [increment] and [binary-to-unary] functions that you
    wrote for the [binary] exercise in the [Basics] chapter.  Prove
    that these functions commute -- that is, incrementing a binary
    number and then converting it to unary yields the same result as
    first converting it to unary and then incrementing.
    Name your theorem [bin_to_nat_pres_incr].

    (Before you start working on this exercise, please copy the
    definitions from your solution to the [binary] exercise here so
    that this file can be graded on its own.  If you find yourself
    wanting to change your original definitions to make the property
    easier to prove, feel free to do so.) *)

(* another style , different from Basic.v *)
Module Playground1.
Inductive bin : Type :=
  (*zero*)
  | O : bin
  (*binary*)
  | B : bin -> bin
  (*one more than binary*)
  | MB : bin -> bin.

Fixpoint incr (n : bin) : bin :=
  match n with
    | O => MB O
    | B n' => MB n'
    | MB n'=> B (incr  n')
  end.

Fixpoint bin_to_nat (n : bin) : nat :=
  match n with
    | O => 0
    | B n' => plus (bin_to_nat n') (bin_to_nat n')
    | MB n' => S (plus (bin_to_nat n') (bin_to_nat n'))
  end.

Theorem bin_to_nat_pres_incr : forall b,
    bin_to_nat(incr b) = S( bin_to_nat(b)).
Proof.
  intros b.
  induction b as [|b' | mb' IHmb'].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. 
    rewrite -> IHmb'.
    rewrite -> plus_n_Sm. 
    simpl. reflexivity.
Qed.



(** [] *)


(** **** Exercise: 5 stars, advanced (binary_inverse)  *)
(** This exercise is a continuation of the previous exercise about
    binary numbers.  You will need your definitions and theorems from
    the previous exercise to complete this one.

    (a) First, write a function to convert natural numbers to binary
        numbers.  Then prove that starting with any natural number,
        converting to binary, then converting back yields the same
        natural number you started with.

    (b) You might naturally think that we should also prove the
        opposite direction: that starting with a binary number,
        converting to a natural, and then back to binary yields the
        same number we started with.  However, it is not true!
        Explain what the problem is.

    (c) Define a "direct" normalization function -- i.e., a function
        [normalize] from binary numbers to binary numbers such that,
        for any binary number b, converting to a natural and then back
        to binary yields [(normalize b)].  Prove it.  (Warning: This
        part is tricky!)

    Again, feel free to change your earlier definitions if this helps
    here. 
*)

(*a*)
Fixpoint division_by_2 (n : nat) : nat :=
  match n with
    | 0 => 0
    | 1 => 0
    | S (S n') => S (division_by_2 n')
  end.

Example test_d_by_2 : division_by_2 1999 = 999.
Proof.
  simpl.
  reflexivity.
Qed.
(*
Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
    | S (S n') => match evenb n' with
                          | true => B (nat_to_bin (division_by_2 (S (S n'))))
                          | false =>  MB (nat_to_bin (division_by_2 (S (S n'))))
                        end
    | 0 => O
    | 1 => MB O
  end.*)

Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
   | 0 => O
   | S n' => incr (nat_to_bin n')
  end.

Example test_d_by_2' : division_by_2 1999 = 999.
Proof.
  simpl.
  reflexivity.
Qed.

End Playground1.

(* FILL IN HERE *)
(** [] *)

(* ###################################################################### *)
(** * Formal vs. Informal Proof (Optional) *)

(** "Informal proofs are algorithms; formal proofs are code." *)

(** The question of what, exactly, constitutes a proof of a
    mathematical claim has challenged philosophers for millennia.  A
    rough and ready definition, though, could be this: a proof of a
    mathematical proposition [P] is a written (or spoken) text that
    instills in the reader or hearer the certainty that [P] is true.
    That is, a proof is an act of communication.

    Acts of communication may involve different sorts of readers.  On
    one hand, the "reader" can be a program like Coq, in which case
    the "belief" that is instilled is a simple mechanical check that
    [P] can be derived from a certain set of formal logical rules, and
    the proof is a recipe that guides the program in performing this
    check.  Such recipes are _formal_ proofs.

    Alternatively, the reader can be a human being, in which case the
    proof will be written in English or some other natural language,
    and will thus necessarily be _informal_.  Here, the criteria for
    success are less clearly specified.  A "good" proof is one that
    makes the reader believe [P].  But the same proof may be read by
    many different readers, some of whom may be convinced by a
    particular way of phrasing the argument, while others may not be.
    One reader may be particularly pedantic, inexperienced, or just
    plain thick-headed; the only way to convince them will be to make
    the argument in painstaking detail.  But another reader, more
    familiar in the area, may find all this detail so overwhelming
    that they lose the overall thread.  All they want is to be told
    the main ideas, because it is easier to fill in the details for
    themselves.  Ultimately, there is no universal standard, because
    there is no single way of writing an informal proof that is
    guaranteed to convince every conceivable reader.  In practice,
    however, mathematicians have developed a rich set of conventions
    and idioms for writing about complex mathematical objects that,
    within a certain community, make communication pretty reliable.
    The conventions of this stylized form of communication give a
    fairly clear standard for judging proofs good or bad.

    Because we are using Coq in this course, we will be working
    heavily with formal proofs.  But this doesn't mean we should
    completely ignore the informal ones!  Formal proofs are useful in
    many ways, but they are _not_ very efficient ways of communicating
    ideas between human beings. *)

(** For example, here is a proof that addition is associative: *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Coq is perfectly happy with this as a proof.  For a human,
    however, it is difficult to make much sense of it.  If you're used
    to Coq you can probably step through the tactics one after the
    other in your mind and imagine the state of the context and goal
    stack at each point, but if the proof were even a little bit more
    complicated this would be next to impossible.  Instead,
    a (pedantic) mathematician might write it something like this: *)
(** - _Theorem_: For any [n], [m] and [p],
      n + (m + p) = (n + m) + p.
    _Proof_: By induction on [n].

    - First, suppose [n = 0].  We must show 
        0 + (m + p) = (0 + m) + p.  
      This follows directly from the definition of [+].

    - Next, suppose [n = S n'], where
        n' + (m + p) = (n' + m) + p.
      We must show
        (S n') + (m + p) = ((S n') + m) + p.
      By the definition of [+], this follows from
        S (n' + (m + p)) = S ((n' + m) + p),
      which is immediate from the induction hypothesis.  _Qed_. *)

(** The overall form of the proof is basically similar.  This is
    no accident: Coq has been designed so that its [induction] tactic
    generates the same sub-goals, in the same order, as the bullet
    points that a mathematician would write.  But there are
    significant differences of detail: the formal proof is much more
    explicit in some ways (e.g., the use of [reflexivity]) but much
    less explicit in others (in particular, the "proof state" at any
    given point in the Coq proof is completely implicit, whereas the
    informal proof reminds the reader several times where things
    stand). *)

(** Here is a formal proof that shows the structure more
    clearly: *)

Theorem plus_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.   Qed.

(** **** Exercise: 2 stars, advanced (plus_comm_informal)  *)
(** Translate your solution for [plus_comm] into an informal proof. *)

(** Theorem: Addition is commutative.
 
    Proof: (* FILL IN HERE *)
*)
(** [] *)

(** **** Exercise: 2 stars, optional (beq_nat_refl_informal)  *)
(** Write an informal proof of the following theorem, using the
    informal proof of [plus_assoc] as a model.  Don't just
    paraphrase the Coq tactics into English!
 
    Theorem: [true = beq_nat n n] for any [n].
    
    Proof: (* FILL IN HERE *) 
[] *)

(** $Date: 2016-01-07 14:17:43 +0000 (Thu, 07 Jan 2016) $ *)
