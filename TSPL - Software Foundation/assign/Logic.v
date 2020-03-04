(** * Logic: Logic in Coq *)

Require Export Tactics.

(** In previous chapters, we have seen many examples of factual
    claims (_propositions_) and ways of presenting evidence of their
    truth (_proofs_).  In particular, we have worked extensively with
    _equality propositions_ of the form [e1 = e2], with
    implications ([P -> Q]), and with quantified propositions ([forall
    x, P]).  In this chapter, we will see how Coq can be used for more
    sophisticated logical reasoning.

    Before diving into details, we should talk a bit about the status
    of mathematical statements in Coq. Recall that Coq is a _typed_
    language, which means that each object we manipulate has an
    associated type. Logical claims are no exception: In Coq, any
    statement we might try to prove has a type, namely [Prop], the
    type of _propositions_. We can see this with the [Check]
    command: *)

Check 3 = 3.
(* ===> Prop *)

Check forall n m : nat, n + m = m + n.
(* ===> Prop *)

(** Note that _all_ propositions have a type in Coq, regardless of
    whether they are true or not. Simply _being_ a proposition is one
    thing; being _provable_ is something else! *)

Check forall n : nat, n = 2.
(* ===> Prop *)

Check 3 = 4.
(* ===> Prop *)

(** The fact that propositions have types is an important aspect of
    Coq's formalism: Propositions are _first-class objects_ that can
    be manipulated according to the same basic principles as the other
    entities of the language.  So far, we've seen one primary place
    that propositions can appear in Coq: in [Theorem] (and [Lemma] and
    [Example]) declarations. *)

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** But propositions can be used in many other ways.  For example, we
    have also seen that we can give a name to a proposition using a
    [Definition], just as we have given names to expressions of other
    sorts. *)

Definition plus_fact : Prop  :=  2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(** We can later use this name in any situation where a proposition is
    expected -- for example, as the claim in a [Theorem] declaration. *)

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity.  Qed.

(** We can also write _parameterized_ propositions -- that is,
    functions that take arguments of some type and return a
    proposition. For instance, the following function takes a number
    and returns a proposition asserting that this number is equal to
    three: *)

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.
(* ===> nat -> Prop *)

(** In Coq, functions that return propositions are said to define
    _properties_ of their arguments.  For instance, here's a
    polymorphic property defining the familiar notion of an _injective
    function_. *)

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. inversion H. reflexivity.
Qed.

(** The equality operator [=] that we have been using so far is also
    just a function that returns a [Prop]. The expression [n = m] is
    just syntactic sugar for [eq n m], defined using Coq's [Notation]
    mechanism. Because [=] can be used with elements of any type, it
    is also polymorphic: *)

Check @eq.
(* ===> forall A : Type, A -> A -> Prop *)

(** (Notice that we wrote [@eq] instead of [eq]: The type argument [A]
    to [eq] is declared as implicit, so we need to turn off implicit
    arguments to see the full type of [eq].) *)

(* #################################################################### *)
(** * Basic Operations *)

(** We have seen a few operations that can be used to define
    propositions in Coq: implication, quantification, equality, and
    function definitions.  We now introduce several more. *)

(** ** Conjunction *)

(** The _conjunction_ or _logical and_ of two propositions [A] and [B]
    is written [A /\ B], denoting the claim that both [A] and [B] are
    true.  (The infix notation is actually just syntactic sugar for
    [and A B], where [and : Prop -> Prop -> Prop].  That is [and] is a
    Coq operator that takes two propositions as arguments and yields a
    proposition.) *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.

(** To prove a conjunction, we use the [split] tactic. Its effect is
    to generate two subgoals, one for each part of the statement: *)

Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(** More generally, the following principle works for any two
    propositions [A] and [B]: *)

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

(** Recall that a logical statement with multiple arrows just denotes
    a theorem that has several hypotheses. Hence, the above theorem
    just means that, for any propositions [A] and [B], if we assume
    that [A] is true and we assume that [B] is true, then we can
    derive that [A /\ B] is also true.

    Since applying a theorem with hypotheses to some goal has the
    effect of generating as many subgoals as there are hypotheses for
    that theorem, we can, if we like, apply [and_intro] to achieve the
    same effect as using the [split] tactic. For instance, here's an
    alternate proof of the first example: *)

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(** **** Exercise: 2 stars (and_exercise)  *)
Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** So much for proving conjunctive statements.  To go in the other
    direction -- i.e., to _use_ a conjunctive hypothesis to prove
    something else -- we employ the [destruct] tactic.  If the proof
    context contains a hypothesis [H] of the form [A /\ B], writing
    [destruct H as [HA HB]] will remove [H] from the context and add
    two new hypotheses: [HA], stating that [A] is true, and [HB],
    stating that [B] is true. For instance: *)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** As usual, we can also destruct [H] when we introduce it instead of
    introducing and then destructing it: *)

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** You may wonder why we bothered packing the two hypotheses [n = 0]
    and [m = 0] into a single conjunction, since we could have also
    stated the theorem with two separate premises: *)

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** While in this example it would arguably work fine to keep the two
    hypotheses separate in the statement of the theorem.  However, it
    is often necessary to explicitly decompose conjunctions that arise
    from intermediate steps in proofs, especially in bigger
    developments. Here's a simplified example: *)

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

(** Another common situation with conjunctions is that we know [A /\
    B] but in some context we need just [A] (or just [B]).  The
    following lemmas are useful in such cases: *)

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP.  Qed.

(** **** Exercise: 1 star, optional (proj2)  *)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Finally, we sometimes need to rearrange the order of conjunctions
    and/or the grouping of conjuncts in multi-way conjunctions.  The
    following commutativity and associativity theorems come in handy
    in such cases. *)

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP.  Qed.
  
(** **** Exercise: 2 stars (and_assoc)  *)
(** In the following proof, notice how the _nested_ intro pattern
    breaks the hypothesis [H : P /\ (Q /\ R)] down into [HP : P], [HQ
    : Q], and [HR : R].  Finish the proof from there: *)

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
(* FILL IN HERE *) Admitted.
(** [] *)

(** ** Disjunction *)

(** An equally important connective is the _disjunction_, or _logical
    or_ of two propositions: [A \/ B] is true when either [A] or [B]
    is.  (Alternatively, we can write [or A B], where [or : Prop ->
    Prop -> Prop]; the symbolic infix form is just syntactic sugar.)

    To use a disjunctive hypothesis in a proof, we proceed by case
    analysis, which, as in the case of [nat] or other data types, can
    be done with the [destruct] or [intros] tactics.  Here is an
    example: *)

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on 
     [n = 0 \/ m = 0] *)
  intros n m [Hn | Hm].
  - (* Here, [n = 0] *)
    rewrite Hn. reflexivity.
  - (* Here, [m = 0] *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

(** We can see in this example that, when we perform case analysis on
    a disjunction [A \/ B], we must then satisfy two proof
    obligations, each showing that the conclusion holds under a
    different assumption ([A] in the first subgoal and [B] in the
    second). Notice that the case analysis pattern ([Hn | Hm]) allows
    us to name the hypothesis that is generated in each subgoal.

    Conversely, to show that a disjunction holds, we need to show that
    one of its sides is true. This is done via two tactics, [left] and
    [right]. As their names imply, the first one requires proving the
    left side of the disjunction, while the second requires proving
    its right side.  Here is a trivial use: *)

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

(** Here is a slightly more interesting example, requiring the use of
    both [left] and [right]: *)

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.



(** **** Exercise: 1 star (mult_eq_0)  *)
Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star (or_commut)  *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  (* FILL IN HERE *) Admitted.

(* !!! *)

Theorem or_distributes_over_and_2 : forall P Q R : Prop, 
   (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof. 
  intros P Q R. intros H0. 
  destruct H0 as [[H1 | H2] [H3 | H4]].
  - (* P \/ Q /\ R *) 
    (* P *) left. apply H1. 
  - (* P \/ Q /\ R *)
    (* P *) left. apply H1.
  - (* P \/ Q /\ R *) 
    (* P *) left. apply H3.
  - (* P \/ Q /\ R *) 
    (* Q /\ R *) right. split. apply H2. apply H4.  
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - (* P \/ Q /\ R -> (P \/ Q) /\ (P \/ R) *)
    intros H. destruct H as [H1 | [H2 H3]].
    + (* (P \/ Q) /\ (P \/ R) *)
       split. 
       { (*P*) left. apply H1. }
       { (*P*) left. apply H1. }
    + (* (P \/ Q) /\ (P \/ R) *)
       split.
       { (*Q*) right. apply H2. }
       { (*R*) right. apply H3. }
  - (* (P \/ Q) /\ (P \/ R) -> P \/ Q /\ R *)
    apply or_distributes_over_and_2.
Qed.

Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q HPQ.
  (*~ Q -> ~ P*)
  unfold not.
  intros HQF HP.
 (*MP : Q -> False  False  |= Q*)
  apply HQF.
 (*MP : P -> Q  P  |= Q*)
  apply HPQ in HP.
  apply HP.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P.
  unfold not.
  intros HPF.
  destruct HPF as [HP HPF'].
  (*MP : P -> False  False  |= P*)
  apply HPF'.
  apply HP.
Qed.

(** [] *)

(** ** Falsehood and Negation *)

(** So far, we have mostly been concerned with proving that certain
    things are _true_ -- addition is commutative, appending lists is
    associative, etc.  But we may also be interested in _negative_
    results -- showing that certain propositions are _not_ true. In
    Coq, such negative statements are expressed with the negation
    operator [~].

    To see how negation works, recall that the idea behind a sound
    logic such as Coq's is that everything that can be proved should
    be true. If we turn this principle on its head, this means that,
    if something is _not_ true, then there must be no way to prove
    it. For instance, it is not possible to show the following
    statement: *)

Example contradiction : 0 = 1.
Proof.
  (* There is nothing we can do here... *)
Abort.

(** Thus, if we want to show that something is _not_ true, we can try
    to argue that it cannot be proved. This is where the special
    contradictory proposition [False] comes into play. Coq's logic
    ensures by construction that [False] cannot be proved without
    additional hypotheses. Therefore, if we want to show that some
    proposition [A] is not true, _it suffices to show that [A] implies
    [False]_. For instance, this is how we state that [0] and [1] are
    different elements of [nat]: *)
(**  This digression through provability seems like hard work.  Is
   there a simpler way? 
 *)

Theorem zero_not_one : 0 = 1 -> False.

(** We can use the [inversion] tactic on the [0 = 1] hypothesis to
    solve this goal; the hypothesis claims that two expressions
    starting with different constructors are equal, and, since there
    are no circumstances under which this could be the case,
    [inversion] will therefore generate no subgoals.  This is just
    another instance of the principle of explosion. *)

Proof.
  intros contra. inversion contra.
Qed.

(** The statement of [zero_not_one] makes sense because, if we were
    able to prove that [0 = 1], we would be able to combine that proof
    with the [zero_not_one] theorem above to derive a complete proof
    of [False], as an instance of this more general theorem: *)
(**  modus_ponens is not used in the rest of the book.  Is it
   important to mention it, or can we delete? 
 *)

Theorem modus_ponens : forall A B : Prop, A -> (A -> B) -> B.
Proof.
  intros A B H1 H2. apply H2. apply H1.
Qed.

(** Thus, since [False] cannot be proved, the same must hold of 
    [0 = 1].

    If we summarize the above discussion in a Coq definition, we
    arrive precisely at the definition of negation in Coq (as usual,
    we give the definition in a sub-module to avoid conflicting with
    the one already present in the global namespace): *)

Module MyNot.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

End MyNot.

(** Combining negation with equality gives us _inequality_: asserting
    [~ (x = y)] is the same as asserting that [x] and [y] are not
    equal. This combination occurs often enough that Coq also provides
    a special notation for it, [x <> y]: *)

Check (0 <> 1).
(* ===> Prop *)

Theorem zero_not_one' : 0 <> 1.
Proof.
  intros H. inversion H.
Qed.

(** Since [False] is a contradictory proposition by construction, the
    principle of explosion also applies to it. If we assume [False] in
    the proof context, we can destruct it to complete any goal: *)
(**  What does it mean to be "contradictory by construction"? 
 *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra.  Qed.

(** The Latin _ex falso quodlibet_ means, literally, "from falsehood
    follows whatever you like"; this is another common name for the
    principle of explosion. *)

(** It takes a little practice to get used to working with negation in
    Coq.  Even though you can see perfectly well why a statement
    involving negation is true, it can be a little tricky at first to
    get things into the right configuration so that Coq can understand
    it!  Here are proofs of a few familiar facts to get you warmed
    up. *)

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H.  Qed.

(** Similarly, since inequality involves a negation, it requires a
    little practice to be able to work with it fluently.  

    Here is one useful trick.  If you are trying to prove a goal that
    is nonsensical (e.g., the goal state is [false = true]), apply
    [ex_falso_quodlibet] to change the goal to simply [False].  This
    change makes it easier to use assumptions of the form [~P] that
    may be available in the context -- in particular, assumptions of
    the form [x<>y]. *)

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

(** Since reasoning with [ex_falso_quodlibet] is quite common, Coq
    provides a built-in tactic, [exfalso], for applying it. *)

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = false *)
    unfold not in H.
    exfalso.                (* <=== *)
    apply H. reflexivity.
  - (* b = true *) reflexivity.
Qed.


Theorem notnot : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H.
  unfold not.
  intro HnotP.
  apply HnotP.
  apply H.
Qed.

(*constructive logic*)


(** ** Truth *)

(** Besides [False], Coq's standard library also defines [True], a
    proposition that can be proved trivially (and hence, is trivially
    true): *)

Lemma True_is_true : True.
Proof. split. Qed.

(** Unlike [False], which we'll use extensively, [True] is used quite
    rarely.  By itself, it is trivial (and therefore uninteresting) to
    prove as a goal, and it carries no useful information as a
    hypothesis. But it can be useful when defining complex [Prop]s
    using conditionals or as a parameter to higher-order [Prop]s.  We
    will see some examples of the use of [True] later on. *)

(** ** Logical Equivalence *)

(** The handy "if and only if" connective, which asserts that two
    propositions have the same truth value, is just the conjunction of
    two implications. *)

Module MyIff.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB.  Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. inversion H'.
Qed.

(** **** Exercise: 1 star, optional (iff_properties)  *)
(** Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)

(* !!! *)

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  split.
  - (*  -> *)
    intros H. apply H.
  - (* <- *)
    intros H. apply H.
Qed.


Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R.
  intros [H0 H1]. intros [H2 H3].
  split.
 -  (* P -> R *)
     intros H. apply H0 in H. apply H2 in H. apply H.
 -  (* R -> P *)
     intros H. apply  H3 in H. apply H1 in H. apply H.
Qed. 

Theorem iff_trans_2 : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R. intros H1 H2.
  split.
 -  (* P -> R *) 
     intros H. apply H1 in H. apply H2 in H. apply H.
 -  (* R -> P *)
     intros H. apply H2 in H. apply H1 in H. apply H.
Qed. 
(** [] *)

(** Some of Coq's tactics treat [iff] statements specially, thus
    avoiding for some low-level manipulation when reasoning with them.
    In particular, [rewrite] and [reflexivity] can be used with [iff]
    statements, not just equalities.  To enable this behavior, we need
    to import a special Coq library: *)

Require Import Coq.Setoids.Setoid.

(** (The term "setoid" is used in mathematics to refer to a set or
    type equipped with an equivalence relation.  Setoids are used in
    Coq to model the standard notion of "quotient sets" -- i.e.,
    instead of forming a new type whose elements are the equivalence
    classes of some existing type under some equivalence relation, in
    Coq we keep the base type and the equivalence relation
    separate.) *)
(**  Is that helpful, or confusing? 
 *)

(** Here is a simple example demonstrating how these basic tactics
    work with [iff].  First, we prove a few basic equivalence
    results: *)

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

(** We can now use these facts with [rewrite] and [reflexivity] to
    come up with better proofs that manipulate equivalences. Here is a
    ternary version of the previous [mult_0] result: *)

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

(** The [apply] tactic can also be used with [<->]. When given an
    equivalence as its argument, [apply] tries to guess which side of
    the equivalence to use, and then applies it. *)

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.

(* ############################################################ *)
(** ** Existential Quantification *)

(** Another important logical connective is _existential
    quantification_.  In Coq, if we want to say that some [x] of type
    [T] exists such that some property [P] is valid, we can write
    [exists x : T, P]. As with the universal quantifier [forall], the
    type annotation [: T] is optional, if Coq is able to infer from
    the context what the type of [x] should be.

    To prove a statement of the form [exists x, P], we must show that
    [P] holds for a suitable choice of value for [x], usually known as
    the _witness_ of the existential. This is done in two steps:
    First, we must explicitly tell Coq which witness [t] to use by
    writing the tactic [exists t]; then, we need to prove that [P]
    holds after replacing all occurrences of [x] by [t]. Here is an
    example: *)

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

(** Conversely, if we have an existential hypothesis [exists x, P] in
    the context, we can destruct it to obtain a witness [x] and a
    hypothesis stating that [P] holds of [x]. As before, we can give
    these elements any name we want. *)

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  apply Hm.  Qed.

(** **** Exercise: 1 star (dist_not_exists)  *)
(** Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold." *)

(* !!! *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
   (* introducts  the atomic staff *)
   intros X P.
   (* hypothesis of implication*) 
   intros HAP.
   unfold not.
   (* hypothesis of implication*) 
   intros HEP.
   destruct HEP as [x HP].
   apply HP. apply HAP.
Qed.
(** [] *)

(** **** Exercise: 2 stars (dist_exists_or)  *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
   intros X P Q.
   split.
   - intros HEPQ. destruct HEPQ as [x HPQ].
     destruct HPQ as [HP | HQ].
     + left. exists x.  apply HP.
     + right. exists x. apply HQ.
   - intros HEPEQ. destruct HEPEQ as [HEP | HEQ].
     + destruct HEP as [x HP].
        exists x. left.  apply HP. 
     + destruct HEQ as [x HQ].
        exists x. right. apply HQ.
Qed.
     
(** [] *)

(* #################################################################### *)
(** * Programming with Propositions

    The operations that we have just seen provide a rich vocabulary
    for defining complex propositions from simpler ones. To illustrate
    this, let's see how to express the claim that an element [x]
    occurs on a list [l]. Notice that this property has a simple
    recursive structure:

    - If [l] is the empty list, then [x] cannot occur on it.

    - Otherwise, [l] is not empty and is of the form [x' :: l']. In
      this case, [x] occurs on [l] if either it is equal to [x'] or if
      it occurs on [l'].

    We can translate this idea directly into a straightforward Coq
    function, [In] (which is also provided by the Coq standard
    library). *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

(** To use [In], we can often proceed directly from its
    definition. Here's a simple example: *)

Example In_example_1 : In 4 [3; 4; 5].
Proof.
  simpl. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  simpl.
  (* Notice the use of the empty pattern to discharge the last
     case immediately. *)
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

(** We can also use more generic, higher-level lemmas: *)

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

(** Although convenient to use in some cases, this style of
    specification has some drawbacks; for instance, it is subject to
    the usual restrictions regarding the definition of recursive
    functions. In the next chapter, we will see how to define
    propositions _inductively_, a different technique with its own set
    of strengths and limitations. *)

(** **** Exercise: 2 stars (In_map_iff)  *)
Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (in_app_iff)  *)

Lemma in_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (All)  *)

(** Recall that functions that return propositions can be seen as
    _properties_ of their arguments. For instance, if [P] has type [nat
    -> Prop], then [P n] states that property [P] holds of [n].

    Drawing inspiration from [In], write a recursive function [All]
    that states that some property [P] holds of all elements of a list
    [l]. To make sure your definition is correct, prove the [All_In]
    lemma below. Your definition should _not_ just restate the
    left-hand side of [All_In]. *)

Fixpoint All {T} (P : T -> Prop) (l : list T) : Prop :=
  (* FILL IN HERE *) admit.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* #################################################################### *)
(** * Explicitly Manipulating Proofs *)

(** One interesting aspect of Coq's formalism that we haven't explored
    is the status it gives to _proofs_. Indeed, Coq's language makes
    it possible to compose proofs of different theorems in a uniform
    way that resembles how we write functional programs in it. *)

(** Let us illustrate this feature with a few examples. We have seen
    that we can use the [Check] command to ask Coq for the type of a
    program or term. We can actually also use [Check] to ask Coq what
    a particular theorem proves. For instance: *)

Check plus_comm.
(* ===> forall n m : nat, n + m = m + n *)

(** We see that Coq prints the statement of the [plus_comm] theorem
    just like it prints the type of a normal term that it checks. The
    reason for that is that Coq effectively treats theorems as
    first-class objects whose type _is_ their statement. Intuitively,
    this makes sense because the statement of a theorem tells us what
    we can use that theorem for, much like the type of a program tells
    us what we can do with that program -- e.g., [nat -> nat -> nat]
    means that we can give two [nat]s as arguments to our program, and
    get a [nat] as its result; [n = m -> n + n = m + m] means that, if
    we assume [n = m], we can derive [n + n = m + m]. Operationally,
    however, this analogy goes even further: by applying a theorem as
    a _function_ to hypotheses with matching types, we can specialize
    the result without having to resort to intermediate assertions.

    Let us consider an example. Suppose we wanted to prove the
    following result: *)

Lemma plus_comm3 :
  forall n m p, n + (m + p) = (p + m) + n.

(** One way of proving this theorem is to rewrite with the [plus_comm]
    theorem twice to make both sides of the statement match. The
    problem, however, is that doing this rewrite naively the second
    time will result in Coq undoing the first one. *)

Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite plus_comm.
  (* We are back where we started... *)

(** One simple way of fixing this problem is to use [assert] to derive
    a specialized version of [plus_comm] that can only be used to
    rewrite exactly where we want. *)

  rewrite plus_comm.
  assert (H : m + p = p + m).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

(** A _better_ alternative, however, is to apply [plus_comm] directly
    to the arguments we want to instantiate it with, much like we
    apply a polymorphic function to a type argument. *)

Lemma plus_comm3_take2 :
  forall n m p, n + (m + p) = (p + m) + n.
Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite (plus_comm m).
  reflexivity.
Qed.

(** You can "use lemmas as functions" in this way with almost all
    tactics that take a lemma name as an argument. Note also that
    lemma application obeys the same syntax as the one for functions;
    thus, it is possible, for example, to supply wildcards as
    arguments to be inferred, and declare some arguments as implicit
    permanently. For instance: *)

Example lem_ap_example :
  forall (n : nat) (ns : list nat),
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H) as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

(* #################################################################### *)
(** * Coq vs. Standard Mathematics *)

(** Despite its expressive power, Coq's formalism differs in several
    aspects from concepts and reasoning principles found in standard
    mathematics. For instance, while a mathematical object can be
    member of potentially many different sets, a term of Coq's logic
    is a member of exactly one type. Often, this discrepancy poses no
    harm: Instead of saying that a natural number [n] belongs to the
    set of even numbers, we might say in Coq that [even n] holds,
    where [even : nat -> Prop] is some property describing even
    numbers. Nevertheless, there are many other cases where
    translating standard mathematical reasoning into Coq can be
    cumbersome or even (without adding more axioms to the core logic)
    impossible. We conclude this chapter with a small list of points
    of divergence between the two worlds. *)

(** ** Propositions and booleans *)

(**  AAA: I'm anticipating some of the discussion on evenness from
   the next chapter here. We can remove/adapt some of the material in
   IndProp.v soon. 
 *)
(** You may have noticed that Coq has two ways of expressing logical
    facts: With _booleans_ (of type [bool]) and with
    _propositions_ (of type [Prop]). For instance, to claim that a
    number [n] is even, we may say that [evenb n] returns [true], or
    that there exists [k] such that [n = double k]. Indeed, the two
    notions of evenness are equivalent; we often say that the boolean
    [evenb n] _reflects_ the proposition [exists k, n = double k]. We
    can easily show this fact with a few auxiliary lemmas (one of
    which is left as an exercise): *)

Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

(** **** Exercise: 3 stars (evenb_double_conv)  *)
Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
  (* Hint: Use the [evenb_S] lemma from [Induction.v]. *)
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

(** Similarly, to state that two numbers [n] and [m] are equal, we can
    say that [n = m], or that [beq_nat n m] returns [true]. As we have
    seen, these two notions are again equivalent. *)

Theorem beq_nat_true_iff : forall n1 n2 : nat,
  beq_nat n1 n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply beq_nat_true.
  - intros H. rewrite H. rewrite <- beq_nat_refl. reflexivity.
Qed.

(** On the other hand, even if boolean and propositional claims can be
    equivalent from a purely logical perspective, we have also seen
    that they often aren't so _operationally_. Equality provides an
    extreme example: Knowing that [beq_nat n m = true] is of little
    help in the middle of a proof; however, if we convert that
    statement to the equivalent form [n = m], we can rewrite with
    it. The case of even numbers is also interesting: When proving the
    backwards direction of [even_bool_prop] (that is, going from the
    propositional to the boolean claim), we could proceed by a simple
    induction on [k] ([evenb_double]), whereas the converse
    ([evenb_double_cons]) required a clever generalization and a more
    complicated proof.

    The more general propositional claims happened to be more useful
    for tackling these examples than their boolean counterparts, but
    this needs not be the case. For instance, we cannot test whether a
    general proposition is true or not in function definitions; as a
    consequence, the following code fragment is rejected: *)

(**  Has Fail been introduced? 
 *)
Fail Definition is_even_prime n :=
  if n = 2 then true
  else false.

(** Coq complains that [n = 2] has type [Prop], while it expects an
    elements of an inductive type such as [bool]. The reason for this
    error message has to do with the _computational_ nature of Coq's
    logic: Coq was designed so that every function that we can write
    in it is computable and total. One reason for that is to allow the
    extraction of executable programs from Coq developments. As a
    consequence, [Prop] in Coq does _not_ have a universal case
    analysis operation telling whether each proposition is true or
    false, since such an operation would allow us to write
    non-computable functions. Indeed, as shown in later chapters, we
    can use Coq's logic to model the execution of computer programs,
    implying that such a case analysis operation would allow us to
    test whether that program halts on all possible inputs or not. As
    computability theory shows, however, no computer program can yield
    that answer.

    Although general non-computable properties cannot be phrased as
    boolean computations, it is worth noting that even many computable
    properties are easier to express using [Prop] than [bool],
    especially in Coq's programming language, where recursive
    functions are subject to important restrictions. For instance, the
    next chapter shows how to define that a regular expression matches
    a given string using [Prop]. Doing the same with [bool] would
    amount to writing a regular expression matcher, which would be
    more complicated, harder to understand and harder to reason about.

    An important side benefit of stating facts through booleans is
    enabling some proof automation through computation with Coq terms,
    a technique known as _proof by reflection_. Consider the following
    statement: *)

Example even_1000 : exists k, 1000 = double k.

(** The most direct proof of this fact is to give the value of [k]
    explicitly. *)

 Proof. exists 500. reflexivity. Qed.

(** On the other hand, the proof of the corresponding boolean
    statement is even simpler: *)

Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed.

(** What is interesting is that, since both notions are equivalent, we
    can use the boolean formulation to prove the other one without
    mentioning 500 explicitly: *)

Example even_1000'' : exists k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.

(** Although we haven't gained much in terms of proof size in this
    case, many proofs are made considerably simpler by the use of
    reflection. As an extreme example, the Coq proof of the 4-color
    theorem uses reflection to reduce the analysis of hundreds of
    different cases to a boolean computation. We won't cover
    reflection in great detail, but it serves as a good example of how
    booleans and general propositions are complementary to each
    other. In many cases, it is good to have multiple equivalent
    formulations of the same property that are more well-suited for
    particular use cases. *)

(** **** Exercise: 2 stars (logical_connectives)  *)

(** The following lemmas relate the propositional connecives studied
    in this chapter to the corresponding boolean operations. *)

Lemma andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** **** Exercise: 1 star (beq_nat_false_iff)  *)

(**  Try to motivate this form, and check that we are indeed using
   it (look also for [beq_id_false_iff]) 
 *)

(* !!! *)

Theorem beq_nat_false_iff' : forall x y : nat,
  beq_nat x y = false
  <-> x <> y.
Proof.
  intros.
  
Qed.

Theorem beq_nat_false_iff : forall x y : nat,
  beq_nat x y = false
  <-> x <> y.
Proof.
  intros x.
  split.
  (*using the experience in Tactics.v: Put the y back*)
  generalize dependent y.
  induction x as [| x' IHx'].
  - (* forall y : nat, beq_nat 0 y = false -> 0 <> y *)
    intros y. destruct y.
    + (*beq_nat 0 0 = false -> 0 <> 0*)
       simpl. intros H. inversion H.
    + (*beq_nat 0 (S y) = false -> 0 <> S y*)
       simpl. unfold not.
       intros H1 H2.
       inversion H2.
  - (* forall y : nat, beq_nat (S x') y = false -> S x' <> y *) 
     intros y. destruct y.
    + simpl. intros H3 H4.
       inversion H4.
    + simpl. unfold not.
       intros H5 H6.
       unfold not in IHx'.
       inversion H6.
       (*generalize is powerful*)
       generalize dependent H0.
       apply IHx'.
       apply H5.
  - (* x <> y -> beq_nat x y = false *)
     generalize dependent y.
     unfold not.
     (*I have to induction x here again. I don't know why.*)
     induction x.
     destruct y.
     + (*(0 = 0 -> False) -> beq_nat 0 0 = false*)
         intros H7.
         simpl. 
         exfalso. 
         apply H7. reflexivity.
     + (*(0 = S y -> False) -> beq_nat 0 (S y) = false*)
        intros. simpl. reflexivity.
     + (*forall y : nat, (S x = y -> False) -> beq_nat (S x) y = false*)
        intros . destruct y.
       * (*beq_nat (S x) 0 = false*)
         simpl. reflexivity.
       * (*beq_nat (S x) (S y) = false*)
         apply IHx.
         intros.
         apply H.
         rewrite H0.
         reflexivity.
Qed.

(** **** Exercise: 3 stars (beq_list)  *)
(** Given a boolean operator [beq] for testing equality of elements of
    some type [A], we can define a function [beq_list beq] for testing
    equality of lists with elements in [A]. Complete the definition of
    the [beq_list] function below. To make sure that your definition
    is correct, prove the [beq_list_true_iff] lemma below. *)

Fixpoint beq_list {A} (beq : A -> A -> bool)
                  (l1 l2 : list A) : bool :=
  (* FILL IN HERE *) admit.

Lemma beq_list_true_iff :
  forall A (beq : A -> A -> bool),
    (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, beq_list beq l1 l2 = true <-> l1 = l2.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** ** Classical vs. constructive logic *)

(** We have seen that it is not possible to test whether a generic
    proposition [P] holds or not in a Coq program. You may be
    surprised to learn that the same restriction applies to _proofs_!
    In other words, the following intuitive reasoning principle is not
    derivable in Coq: *)

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

(** To understand operationally why this is the case, recall that,
    when proving a statement of the form [P \/ Q], we had to use the
    [left] and [right] tactics, which effectively require knowing
    which side of the disjunction holds. However, the universally
    quantified [P] in [excluded_middle] is an _arbitrary_ proposition,
    which we know nothing about. We don't have enough information to
    choose which of [left] or [right] to apply, just like Coq doesn't
    have enough information to mechanically decide whether [P] holds
    or not inside a function. On the other hand, if we happen to know
    that [P] is reflected in some boolean term [b], then knowing
    whether it holds or not is trivial: we just have to check the
    value of [b]. This leads to the following theorem: *)

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. inversion contra.
Qed.

(** In particular, the excluded middle is valid for equations [n = m],
    between natural numbers [n] and [m].

    You may find it strange that the general excluded middle is not
    available in Coq, given that any claim can only be true or
    false. Nonetheless, there is one advantage in not assuming the
    excluded middle by default: statements in Coq can make stronger
    claims than the analogous statements in standard
    mathematics. Notably, whenever there is a Coq proof of [exists x,
    P x], it is possible to explicitly exhibit a well-defined value of
    [x] for which we can prove [P x] -- in other words, every proof of
    existence of a certain object is necessarily constructive. Because
    of this, logics like Coq's, which do not assume the excluded
    middle, are referred to as _constructive_. More conventional
    logical systems, in which the excluded middle does hold for
    arbitrary propositions, are usually referred to as _classical_.

    The following example shows why assuming the excluded middle may
    lead to non-constructive proofs:

    _Claim_: There exist irrational numbers [a] and [b] such that [a ^
    b] is rational.

    _Proof_: It is not difficult to show that [sqrt 2] is
    irrational. If [sqrt 2 ^ sqrt 2] is irrational, it suffices to
    pose [a = b = sqrt 2] and we are done. Otherwise, [sqrt 2 ^ sqrt
    2] is rational. In this case, we can pose [a = sqrt 2 ^ sqrt 2]
    and [b = sqrt 2], since [a ^ b = sqrt 2 ^ (sqrt 2 * sqrt 2) = sqrt
    2 ^ 2 = 2].

    Can you notice what happened here? We used the excluded middle
    implicitly to consider separately the cases where [sqrt 2 ^ sqrt
    2] is rational or not, without being able to tell which one
    actually holds. Because of that, we cannot determine what the
    precise values of [a] and [b] are.

    As wonderful as constructive logic is, it does have its
    limitations: There are many statements that can easily be proven
    in classical logic but that have much more complicated
    constructive proofs... if indeed they have any constructive proof
    at all! *)

Theorem classic_double_neg : forall P : Prop,
  ~~P -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not in H.
  (* But now what? There is no way to "invent" evidence for [~P]
     from evidence for [P]. *)
Abort.

(** **** Exercise: 5 stars, advanced, optional (classical_axioms)  *)
(**  Maybe put this exercise last? 
 *)
(** For those who like a challenge, here is an exercise taken from the
    Coq'Art book (p. 123).  Each of the following four statements,
    together with [excluded_middle], can be considered as
    characterizing classical logic.  We can't prove any of them in
    Coq, but we can (consistently) add any one of them as an unproven
    axiom if we wish to work in classical logic.

    Prove that all five propositions are equivalent. *)

Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.
Definition classic := forall P:Prop,
  ~~P -> P.
Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).

(* !!! *)

(* I supposed excluded_middle must be true at first.
    I am not sure if this is a correct way or not.*)
Theorem classic_excluded_middle: forall P : Prop,
    excluded_middle -> (excluded_middle <-> classic).
Proof.
  unfold excluded_middle.
  unfold classic.
  intro. 
  split.
  - intros. destruct H with (P0).
    + apply H2. 
    + unfold not in H1. 
       unfold not in H2.
       exfalso. apply H1.
       apply H2.
  - intros. 
    unfold not.
    unfold not in H.
    destruct H with (P0).
    + left. apply H1.
    + right. apply H1.
Qed.
(*I will prove others later.*)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars (excluded_middle_irrefutable)  *)
(** The following theorem implies that it is always safe to assume a
    decidability axiom (i.e., an instance of excluded middle) for any
    _particular_ Prop [P].  Why? Because we cannot prove the negation
    of such an axiom; if we could, we would have both [~ (P \/ ~P)]
    and [~ ~ (P \/ ~P)], a contradiction. *)

Theorem excluded_middle_irrefutable:  forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  (* FILL IN HERE *) Admitted.


(** **** Exercise: 3 stars, optional (not_exists_dist)  *)
(** It is a theorem of classical logic that the following two
    assertions are equivalent:
    ~ (exists x, ~ P x)
    forall x, P x
    The [dist_not_exists] theorem above proves one side of this
    equivalence. Interestingly, the other direction cannot be proved
    in constructive logic. Your job is to show that it is implied by
    the excluded middle.
*)

(* !!! *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros.
  unfold excluded_middle in H.
  unfold not in H, H0.
  destruct H with (P := P x).
  - apply H1.
  - destruct H0. (*I just tried this tactic, but I don't know why it does work.*)
    exists x.
    apply H1.
Qed.

(** [] *)

(** $Date: 2015-08-11 12:03:04 -0400 (Tue, 11 Aug 2015) $ *)
