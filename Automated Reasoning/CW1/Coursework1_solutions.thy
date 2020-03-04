(*<*)
theory Coursework1_solutions
imports Main

begin
(*>*)

section {* Introduction *}

text {* This is the first coursework assignment for the Automated
Reasoning course. It is divided into two parts. In the first part,
you will get some experience with the rules of natural deduction,
building on the exercises that are on the course web page. In the
second part, you will work on a verification task,
using Isabelle's more powerful proof tools in order to prove theorems
about an inductively defined data structure. You will also get to 
formalise your own definitions.

There are two (essentially identical) versions of this document. The
source version, which you can load into Isabelle to complete your proofs:

\quad \url{http://www.inf.ed.ac.uk/teaching/courses/ar/coursework/Coursework1.thy}

and the PDF version, which is easier to read:

\quad \url{http://www.inf.ed.ac.uk/teaching/courses/ar/coursework/Coursework1.pdf}

You should fill in the source version with your proofs for
submission. Submission instructions are at the end of this document. 

The deadline for submission is \textbf{4pm, Friday 26th February 2016}. *}

section {* Marks *}

text {* You will only earn marks for an unfinished proof if you
provide some explanation as to your proof strategy or an explanation
as to why you are stuck. You may also earn marks if you can prove the
theorem by asserting a sensible lemma with \texttt{lemma} and
``proving'' it with the ``cheat'' command \texttt{sorry}. Be careful
to note the restrictions on the proof methods that your are allowed to
use for each question. *}

section {* Background Reading *}

text {* This assignment uses the interactive theorem prover Isabelle,
introduced in the lectures and exercises. 

As you will be using Isabelle interactively, you will need to be
familiar with the system before you start. Formalized mathematics is
not trivial! You will find this assignment much easier if you attend
the lectures, attempt the various Isabelle exercises given on the
course webpages, and ask questions about using Isabelle before you
start. It is recommended that you read Chapter 5 of the Isabelle/HOL
tutorial located at:

\quad \url{http://isabelle.in.tum.de/doc/tutorial.pdf}

We also recommend that you use the Isabelle Cheat Sheet from Jeremy Avigad, which
can be found at:

\quad \url{http://www.inf.ed.ac.uk/teaching/courses/ar/FormalCheatSheet.pdf}
*}

section {* Part 1 : Natural Deduction in Isabelle/HOL (30 marks) *}

text {* In this section, you will get some practice with natural
deduction by proving some theorems from propositional and first-order
logic. Each of these theorems could be solved directly with Isabelle's
automatic tactics, but here, you are asked to use only the following
basic introduction and elimination rules:

\bigskip

\begin{tabular}{lcl}
  conjI &:& @{thm conjI} \\
  conjE &:& @{thm conjE} \\
  conjunct1 &:& @{thm conjunct1} \\
  conjunct2 &:& @{thm conjunct2} \\
  disjI1 &:& @{thm disjI1} \\
  disjI2 &:& @{thm disjI2} \\
  disjE &:& @{thm disjE} \\
  impI &:& @{thm impI} \\
  impE &:& @{thm impE} \\
  mp &:& @{thm mp} \\
  notI &:& @{thm notI} \\
  notE &:& @{thm notE} \\
  iffI &:& @{thm iffI} \\
  iffE &:& @{thm iffE} \\
  iffD1 &:& @{thm iffD1} \\
  iffD2 &:& @{thm iffD2} \\
  allI &:& @{thm allI} \\
  allE &:& @{thm allE} \\
  spec &:& @{thm spec} \\
  exI &:& @{thm exI} \\
  exE &:& @{thm exE} \\
\end{tabular}

\bigskip


You may also use the following \emph{classical rules}:

\bigskip

\begin{tabular}{lcl}
  excluded\_middle &:& @{thm excluded_middle} \\
  ccontr &:& @{thm ccontr}
\end{tabular}

\bigskip

Note that you can display any of these theorems, and any other named
theorem, even while in the middle of a proof. For instance, to display
the rule \texttt{conjI}, just use the following command: 
\begin{displaymath}
  \texttt{thm conjI}
\end{displaymath}

In each step of the proof, you may use apply with any of the methods
\texttt{rule}, \texttt{erule}, \texttt{drule}, \texttt{frule}, and
their variants \texttt{rule\_tac}, \texttt{erule\_tac},
\texttt{drule\_tac} and \texttt{frule\_tac}. You will also need to use
the method \texttt{assumption}, and you may also use the commands
\texttt{defer} and \texttt{prefer} to manipulate the goal-stack during
a proof. You are \textbf{not} permitted to use any other proof methods for this
part.

Prove the following lemmas by replacing the placeholder proof \texttt{oops}
with a real proof in each case: \clearpage *}

lemma "P \<longrightarrow> P"
by (rule impI)
text {* \hfill (1 marks) *}

lemma "P \<and> Q \<longrightarrow> Q \<and> P"
apply (rule impI)
apply (erule conjE)
by (rule conjI)
text {* \hfill (1 mark) *}

lemma "(Q \<and> R) \<and> P \<longrightarrow> (P \<and> R) \<and> Q"
apply (rule impI)
apply (erule conjE)+
by (rule conjI)+
text {* \hfill (1 mark) *}

lemma "(Q \<or> R) \<and> P \<longrightarrow> \<not> P \<longrightarrow> Q"
apply (rule impI)+
apply (erule conjE)
by (erule notE)
text {* \hfill (1 mark) *}

lemma "(\<forall>x. P x \<longrightarrow> Q x) \<longrightarrow> \<not> (\<exists>x. P x \<and> \<not> Q x)"
apply (rule impI)
apply (rule notI)
apply (erule exE, erule_tac x="x" in allE)
apply (erule conjE)
apply (drule_tac P="P x" in mp, assumption)
by (erule notE)
text {* \hfill (5 marks) *}

lemma "(\<exists>x. \<forall>y. P x y) \<longrightarrow> (\<forall>y. \<exists>x. P x y)"
apply (rule impI)
apply (rule allI, erule exE)
apply (erule_tac x="y" in allE)
by (rule_tac x="x" in exI)
text {* \hfill (5 marks) *}

lemma "\<not> (\<exists>barber. man barber \<and> (\<forall>x. man x \<and> \<not> shaves x x \<longleftrightarrow> shaves barber x))"
apply (rule notI)
apply (erule exE)
apply (erule conjE)
apply (erule_tac x="barber" in allE)
apply (erule iffE)
apply (erule_tac P="shaves barber barber" in impE)
apply (rule ccontr)
apply (drule_tac P="man barber" and Q="\<not> shaves barber barber" in conjI, assumption)
apply (drule_tac P=" man barber \<and> \<not> shaves barber barber" in mp, assumption)
apply (erule notE, assumption)
apply (frule_tac P=" man barber \<and> \<not> shaves barber barber" in mp, assumption)
by (erule conjE, erule notE)
text {* \hfill (8 marks) *}

lemma "(\<forall>(x::int). (\<exists>y. P x y) \<longrightarrow> Q x) \<and> (\<forall>R (x::int) y. R x y \<longrightarrow> R y x) \<longrightarrow> (\<forall>z. P a z \<longrightarrow> Q z)"
apply (rule impI)
apply (erule conjE)
apply (rule allI)
apply (erule_tac x="z" in allE)
apply (erule_tac x="P" in allE)
apply (erule_tac x="a" in allE)
apply (erule_tac x="z" in allE)
apply (rule impI)
apply (erule impE)
by (rule_tac x="a" in exI, erule mp)
text {* \hfill (8 marks) *}


section {* Part 2. Binary Space Partitioning (70 marks) *}

text {* In this part of the assignment, we will look at a software verification exercise, and 
formally verify properties of a binary tree data structure 
(see \url{http://en.wikipedia.org/wiki/Binary_tree}).

Our binary trees will be used to define a region of space by recursively performing 
\emph{binary partitions}. This technique is typically used in computer graphics and simulations, 
to provide a fast way to compute \emph{collisions} with the defined regions, and to determine 
which objects are potentially visible to a virtual camera. 
  
Our binary trees will consider a one-dimensional case. They recursively partition a line segment 
into disjoint pieces. At each branch of the tree, the line-segment is divided in half, so that 
for a tree of depth $n$, we are able to consider $2^n$ possible subdivisions. At the leaves of the 
tree, we specify whether the corresponding partition is Empty of points, or whether it is Filled 
with points. See Figure~\ref{fig:partition} for an example.

For more information on partitioning in this way, see \url{http://en.wikipedia.org/wiki/Quadtree}, 
where the two-dimensional case is considered. *}

text_raw {* 
\vspace{0.5cm} \begin{figure}[h!]
  \centering
	\includegraphics[scale=0.2]{Partition.pdf}
  \caption{Binary space partitioning in one dimension}
  \label{fig:partition}
\end{figure} \vspace{0.5cm}
*}

text {* The following defines the \emph{datatype} of our binary partition trees. A tree is either 
an Empty or a Filled \emph{leaf}, or else it is a \emph{Branch}, splitting the space into two 
partitions. *}
datatype partition = Empty | Filled | Branch partition partition

text {* Since partitions define parts of a line-segment, it is possible to define a union and 
intersection operation on them, where we understand the arguments to these functions as 
partitions of the same arbitrary segment. Here is the definition of the union function, which we 
can also write with the infix notation @{text "\<squnion>"}, written as \texttt{\textbackslash{}<squnion>}
in Isabelle. *}
fun union :: "partition \<Rightarrow> partition \<Rightarrow> partition" (infixr "\<squnion>" 65) where
   "union (Empty) q = q"
 | "union (Filled) q = Filled"
 | "union p (Empty) = p"
 | "union p (Filled) = Filled"
 | "union (Branch l1 r1) (Branch l2 r2) = Branch (union l1 l2) (union r1 r2)"

text {*  Here is the definition of an intersection function, which we can also write as
@{text "\<sqinter>"} (\texttt{\textbackslash{}<sqinter>}).*}
fun intersect :: "partition \<Rightarrow> partition \<Rightarrow> partition" (infixr "\<sqinter>" 65) where
   "intersect (Empty) q = Empty"
 | "intersect (Filled) q = q"
 | "intersect p (Empty) = Empty"
 | "intersect p (Filled) = p"
 | "intersect (Branch l1 r1) (Branch l2 r2) = Branch (intersect l1 l2) (intersect r1 r2)"

text {* Finally, here is a function to \emph{invert} or \emph{complement} a partition. *}
fun invert :: "partition \<Rightarrow> partition" where
   "invert (Empty) = Filled"
 | "invert (Filled) = Empty"
 | "invert (Branch l r) = Branch (invert l) (invert r)"

subsection {* Simple Proofs by Induction (5 marks) *}
text {* For this first proof, you will use the rules of natural deduction from Part 1 and
equational rules given below. In addition, you will have some rules which are automatically 
proven by Isabelle, based on the data-type and function definitions above. These rules will help 
you simplify expressions involving these functions, and consider the cases which define each of 
their equations. *}

text {* The rules are named @{text partition.induct}, @{text union.simps}, @{text intersect.simps}, 
@{text invert.simps}, @{text union.cases}, @{text intersect.cases} and @{text invert.cases}. 
You can use the @{text thm} command to display these rules. Now, with these new rules, and the 
same basic proof methods used in Part 1, prove that the operation @{text invert} is self-inverse.

Additionally, you might find useful these rules which help reasoning about equality:

\begin{tabular}{lcl}
  refl &:& @{thm refl} \\
  sym &:& @{thm sym} \\
  trans &:& @{thm trans} \\
  subst &:& @{thm subst} \\
\end{tabular}

For this question, you cannot use the @{text auto}, @{text blast} or @{text simp} methods.
*}

text {* \emph{You are provided below with a proof for this theorem, written in an earlier version of
Isabelle. For this question, you have the possibility of trying to fix this proof or to try to
write a proof of your own.}  *}

theorem invert_invert: "\<forall>p. invert (invert p) = p"
  apply (rule allI)
  apply (rule partition.induct)
  apply (rule_tac ?t="invert Empty" in subst)
  apply (rule sym)
  apply (rule invert.simps)+
  apply (rule_tac ?t="invert Filled" in subst)
  apply (rule sym)
  apply (rule invert.simps)+
  apply (rule_tac ?t="invert (Branch x1 x2)" in subst)
  apply (rule sym)
  apply (rule invert.simps)+
  apply (rule_tac ?t="invert (Branch (invert x1) (invert x2))" in subst)
  apply (rule sym)
  apply (rule invert.simps)+
  apply (drule sym)
  apply (drule_tac ?t="x2" in sym)
  apply (erule subst)+
  by (rule refl)

text {* \hfill (5 marks) *}


subsection {* Using More Powerful Proof Methods (10 marks) *}
text {* In proofs such as these, it is usually much easier to use the following tactics. From 
here on, you may use them freely: 
  \hspace{1cm}\\
  @{text case_tac} : perform case-analysis on a given variable.\\
  @{text induct_tac} : apply an induction rule on a given variable.\\
  @{text simp} : the (contextual) rewriter \\
  @{text auto} : the classical reasoner.\\
  @{text blast} : a powerful tableau-prover for first-order reasoning.
  \hspace{1cm}\\

  The \emph{simplifier} deserves particular mention. It is a powerful automated tool that tries 
to rewrite terms as much as possible. It is particularly useful because it already knows a basic 
set of equations with which to rewrite terms. Though you can explicitly supply your own theorems 
with @{text add}, the simplifier already knows plenty of rewrites, including 
@{text union.simps}, @{text intersect.simps} and @{text invert.simps}. With this tool, proofs 
become much shorter: *}
theorem invert_invert_simp: "\<forall>p. invert (invert p) = p"
apply auto
apply (induct_tac p)
by simp+

text {* Note that @{text auto} also performs some simplification, before attempting to solve the
goal. As with @{text "(simp add: <lemma>)"}, you can supply your own simplification rules when 
using @{text auto}, with the command @{text "(auto simp: <lemma>)"}. *}

text {* A proof of the De Morgan law for our functions is provided below: *}

theorem demorgan: "\<forall>p1 p2. (invert p1) \<sqinter> (invert p2) = invert (p1 \<squnion> p2)"
  apply (rule allI)
  apply (induct_tac p1)
  apply auto
  apply (case_tac p2)
  by simp+

text {* Using the lemma \emph{demorgan} and any other appropriate lemmas, prove the following
theorem (without using the \emph{metis} tactic). Note that you 
\emph{must} make use of \emph{demorgan} in your proof.  *}
theorem demorgan2: "\<forall>p1 p2. (invert p1) \<squnion> (invert p2) = invert (p1 \<sqinter>  p2)"
apply (rule allI)+
apply (subgoal_tac "invert (invert (invert p1) \<sqinter> invert (invert p2)) = (invert p1) \<squnion> (invert p2)")
apply (simp add: invert_invert)
apply (simp add: demorgan)
by    (simp add: invert_invert)
text {* \hfill (10 marks) *}


subsection {* Formalising and Proving Properties of Partitions (10 marks)*}
text {* So far, definitions for the \emph{partition} type and various functions and lemmas about
them have been given to you and you were asked to prove them. This part of the coursework is a
small formalisation exercise in which you are asked to write some definitions and lemmas of 
your own before attempting to prove them. When doing formalised mathematics, laying down these 
definitions is often the hardest part. The choices made at this stage can have a significant impact 
on the difficulty of proving the subsequent theorems.*}

text {* First, define a function \emph{mirror}, which, given a \emph{partition}, returns the same 
partition, in which the order of the children in branches has been swapped. *}

fun mirror :: "partition \<Rightarrow> partition" where
   "mirror (Filled) = Filled"
 | "mirror (Empty) = Empty"
 | "mirror (Branch p q) = Branch (mirror q) (mirror p)"
text {* \hfill (2 marks) *}

text {* Then, write down and prove theorems which verify the following properties of 
\emph{mirror}: 

\begin{enumerate}
   \item Mirroring a partition twice results in the original partition.
   \item First mirroring and then inverting a partition is the same as first inverting and then
         mirroring it.
   \item The mirror of the union of two partitions is the same as the union of the mirrors of each
         partition.
   \item The same property as (3), but for intersection.
\end{enumerate} *}

theorem "\<forall>p. mirror (mirror p) = p"
apply (rule allI)
by (induct_tac p, auto)

theorem "\<forall>p. invert (mirror p) = mirror (invert p)"
apply (rule allI)
by (induct_tac p, auto)

theorem "\<forall>p q. mirror (p \<squnion> q) = (mirror p) \<squnion> (mirror q)"
apply (rule allI)
apply (induct_tac p, auto)
by (case_tac q, auto)

theorem "\<forall>p q. mirror (p \<sqinter> q) = (mirror p) \<sqinter> (mirror q)"
apply (rule allI)
apply (induct_tac p, auto)
by (case_tac q, auto)
text {* \hfill (8 marks) *}


subsection {* Simplifying Partitions (45 marks) *}
text {* We'll now consider a function which will \emph{simplify} (or normalise) a partition. 
This function is useful because, as you may have noticed, it is possible for there to be many 
different but \emph{equivalent} ways to express a partition as a tree 
(see Figure~\ref{fig:equivalent}). *}

text_raw {* 
\begin{figure}[h!]
  \centering
	\includegraphics[scale=0.2]{Equivalent.pdf}
  \caption{Different binary trees representing equivalent space partitions}
  \label{fig:equivalent}
\end{figure}
*}

text {* Let us define two functions to reduce these equivalent trees to the same tree: *}
fun simplify1 :: "partition \<Rightarrow> partition" where
"simplify1 (Filled)  = Filled"
| "simplify1 (Empty)  = Empty"
| "simplify1 (Branch (Filled) (Filled)) = Filled"
| "simplify1 (Branch (Empty) (Empty)) = Empty"
| "simplify1 p = p"

fun simplify :: "partition \<Rightarrow> partition" where
"simplify (Filled) = Filled"
| "simplify (Empty) = Empty"
| "simplify (Branch (Filled) (Filled)) = Filled"
| "simplify (Branch (Empty) (Empty)) = Empty"
| "simplify (Branch p q) = simplify1 (Branch (simplify p) (simplify q))"

text {* How can we be sure that these functions are correct? One obvious property is that 
they must preserve the effects of all of our operations. We can make a start towards formally 
verifying this by proving some theorems.  

\clearpage
Prove that, under normalisation, a partition unified with its inverse will always result in
the identity element for unification, which is \emph{Filled}:*}
   
  lemma simplify_branch: 
  "\<lbrakk>(simplify p) = Filled; (simplify q) = Filled\<rbrakk> \<Longrightarrow> simplify (Branch p q) = Filled"
  apply (case_tac p, auto)
  by (case_tac q, auto)
   
theorem "\<forall>p. simplify (p \<squnion> (invert p)) = Filled"
apply (rule allI)
apply (induct_tac p)
by (auto simp: simplify_branch)
text {* \hfill (5 marks) *}

text {*Note that intersection and \emph{Empty} behave in the same way. Now, prove that simplifying
the inverse of a partition has the same result as inverting its simplification:*}
  lemma simplify1: "\<forall>p1 p2. simplify (Branch p1 p2) = simplify1 (Branch (simplify p1) (simplify p2))"
  apply (rule allI)+
  apply (case_tac p1, auto)
  by    (case_tac p2, auto)+

  lemma simplify1_invert: "\<forall>p. invert (simplify1 p) = simplify1 (invert p)"
  apply (rule allI)
  apply (case_tac p, auto)
  apply (case_tac x31, auto)
  by    (case_tac x32, auto)+

lemma simplify_invert: "\<forall>p. simplify (invert p) = invert (simplify p)"
apply (rule allI)
apply (induct_tac p)
by (auto simp: simplify1 simplify1_invert)
text {* \hfill (10 marks) *}

text {* Next, we will consider the union operation. Here is a conjecture we might, mistakenly, 
try to prove: *}

theorem simplify_union_wrong: "simplify p \<squnion> simplify q = simplify (p \<squnion> q)"
oops

text {* However, Isabelle's QuickCheck tool should automatically provide you with a counterexampe
which demonstrates that this conjecture is false. *}

text {* The correct theorem requires an extra simplification on the left-hand side. Your next task 
is to formally verify it. However, you will probably need to prove additional lemmas to make a 
start. There are multiple paths when it comes to proving this theorem. Think carefully about the lemmas
that you will need in order to construct a  proof. *}

  lemma simplify_fix: "\<forall>p. simplify (simplify1 p) = simplify p"
  apply (rule allI)
  apply (case_tac p, auto)
  apply (case_tac x31, auto)
  by    (case_tac x32, auto)+

  lemma simplify_simplify: "\<forall>p. simplify (simplify p) = simplify p"
  apply (rule allI)
  apply (induct_tac p)
  by (auto simp : simplify_fix simplify1)

  lemma union_comm: "\<forall>p1 p2. p1 \<squnion> p2 = p2 \<squnion> p1"
  apply (rule allI)
  apply (induct_tac p1, auto)
  by    (case_tac p2, auto)+

  lemma branch_ff_union: "\<forall>p. simplify (Branch Filled Filled \<squnion> p) = Filled"
  by (auto, case_tac p, auto)
  
  lemma branch_ee_union: "\<forall>p. simplify (Branch Empty Empty \<squnion> p) = simplify p"
  by (auto, case_tac p, auto)

  lemma simplify1_union: "\<forall>p1 p2. simplify (simplify1 p1 \<squnion> p2) = simplify (p1 \<squnion> p2)"
  apply (rule allI)+
  apply (case_tac p1, auto)
  apply (case_tac x31, auto)
  apply (case_tac x32, auto simp: branch_ee_union)
  by    (case_tac x32, auto simp: branch_ff_union)

  lemma simplify1_union2: "\<forall>p1 p2. simplify (simplify1 p1 \<squnion> simplify1 p2) = simplify (p1 \<squnion> p2)"
  apply (auto simp: simplify1_union)
  apply (subst union_comm)
  apply (auto simp: simplify1_union)
  by    (auto simp: union_comm)

theorem simplify_union: "\<forall>p1 p2. simplify (simplify p1 \<squnion> simplify p2) = simplify (p1 \<squnion> p2)"
apply (rule allI)
apply (induct_tac p1)
apply (auto simp: simplify_simplify)
apply (case_tac p2)
apply (simp add: union_comm simplify_simplify)+
by    (simp add: simplify1 simplify1_union2)
text {* \hfill (30 marks) *}

end
(*>*)
