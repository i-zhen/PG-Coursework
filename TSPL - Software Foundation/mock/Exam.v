(* ********************************************** *)
(* Types and Semantics for Programming Languages  *)
(* ********************************************** *)

(* Place an X in front of the appropriate statement *)
(* [ ]  I have done Problems 1 and 2 *)
(* [ ]  I have done Problems 1 and 3 *)


Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.
Require Export Maps.
Require Export SfLib.

(* ********************************************** *)
(* Problem 1 *)
(* ********************************************** *)

Inductive break {X : Type} : list X -> X -> list X -> Prop :=
  | break_eq : forall x xs,
    break (x :: xs) x xs
  | break_cons : forall x y xs ys,
    break xs y ys -> break (x :: xs) y (x :: ys).

Example a : break [1;2;3] 1 [2;3].
Proof.
  apply break_eq.
Qed.

Example b : break [1;2;3] 2 [1;3].
Proof.
  apply break_cons.
  apply break_eq.
Qed.

Example c : break [1;2;3] 3 [1;2].
Proof.
  apply break_cons.
  apply break_cons.
  apply break_eq.
Qed.

Theorem break_in : forall (X : Type) (x y : X) (xs ys : list X),
  break xs y ys -> In x xs -> x = y \/ In x ys.
Proof.
  intros.
  induction H.
 + inversion H0. subst.
   - left. reflexivity.
   - right. assumption. 
 + inversion H0. subst.
   - right. constructor. reflexivity.
   - apply IHbreak in H1.
     destruct H1.
     * left. assumption.
     * right. apply in_cons. assumption.
Qed.

(* ********************************************** *)
(* Problem 2 *)
(* ********************************************** *)

(* Arithmetic and boolean expressions *)

Definition state := total_map nat.

Definition ble_nat := leb.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => ble_nat (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

(* Commands *)

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CLoop : id -> aexp -> com -> com
  | CFor : id -> aexp -> aexp -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'LOOP' x 'TO' a2 'DO' c 'END'" :=
  (CLoop x a2 c) (at level 80, right associativity).
Notation "'FOR' x '==' a1 'TO' a2 'DO' c 'END'" :=
  (CFor x a1 a2 c) (at level 80, right associativity).

(* Evaluation relation *)

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st || st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st || (t_update st x n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  || st' ->
      c2 / st' || st'' ->
      (c1 ;; c2) / st || st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st || st
  | E_WhileLoop : forall st st' st'' b c,
      beval st b = true ->
      c / st || st' ->
      (WHILE b DO c END) / st' || st'' ->
      (WHILE b DO c END) / st || st''
  | E_For : forall x a2 c a1 n st' st'' st,
      aeval st a1 = n ->
      t_update st x n = st' ->
      (LOOP x TO a2 DO c END) / st' || st'' ->
      (FOR x == a1 TO a2 DO c END) / st || st''
  | E_LoopEnd : forall x st a2 c,
      st x > aeval st a2 ->
      (LOOP x TO a2 DO c END) / st || st
  | E_LoopLoop : forall x a2 c st st' st'' st''',
      st x <= aeval st a2 ->
      c / st || st' ->
      t_update st' x (st' x+1) = st'' ->
      (LOOP x TO a2 DO c END) / st'' || st''' ->
      (LOOP x TO a2 DO c END) / st || st'''

  where "c1 '/' st '||' st'" := (ceval c1 st st').

(* Assertions *)

Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" :=
  (assert_implies P Q) (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

(* Hoare triples *)

Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
       c / st || st'  ->
       P st  ->
       Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

(* Assertions *)

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.

(* Assignment *)

(*
             ------------------------------ (hoare_asgn)
             {{Q [X |-> a]}} X::=a {{Q}}
*)


Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (t_update st X (aeval st a)).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.  Qed.

(* Consequence *)

(*
                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
*)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st'). 
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP. 
  apply Himp.
  apply (Hhoare st st'). 
  assumption. assumption. Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  apply hoare_consequence_pre with (P' := P').
  apply hoare_consequence_post with (Q' := Q').
  assumption. assumption. assumption.  Qed.

(* Skip *)

(*
             --------------------  (hoare_skip)
             {{ P }} SKIP {{ P }}
*)

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.  Qed.

(* Sequencing *)

(*
               {{ P }} c1 {{ Q }} 
               {{ Q }} c2 {{ R }}
              ---------------------  (hoare_seq)
              {{ P }} c1;;c2 {{ R }}
*)

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. Qed.

(* Conditional *)

(*
              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} IFB b THEN c1 ELSE c2 FI {{Q}} 
*)

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst. 
  + (* "b is true" *)
    apply (HTrue st st'). 
      assumption. 
      split. assumption. 
             apply bexp_eval_true. assumption.
  + (* "b is false" *)
    apply (HFalse st st'). 
      assumption. 
      split. assumption.
             apply bexp_eval_false. assumption. Qed.

(* While *)

(*
               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~b}}
    The proposition [P] is called an _invariant_ of the loop.
*)

Lemma hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  (* Like we've seen before, we need to reason by induction 
     on [He], because, in the "keep looping" case, its hypotheses 
     talk about the whole loop instead of just [c]. *)
  remember (WHILE b DO c END) as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  + (* Case "E_WhileEnd" *)
    split. assumption. apply bexp_eval_false. assumption.
  + (* Case "E_WhileLoop" *)
    apply IHHe2. reflexivity.
    apply (Hhoare st st'). assumption.
      split. assumption. apply bexp_eval_true. assumption.
Qed.

Theorem hoare_for : forall P Q X c a1 a2,
  {{P}} LOOP X TO a2 DO c END {{Q}} ->
  {{P[X |-> a1]}} FOR X == a1 TO a2 DO c END {{Q}}.
Proof.
  intros P Q X c a1 a2 Hhoare st st' He HP.
  inversion He. subst.
  apply (Hhoare (t_update st X (aeval st a1)) st').
  - assumption.
  - assumption.
Qed.

Theorem hoare_loop : forall P X c a2,
  {{ fun st => P st /\ st X <= aeval st a2}} c {{P[X |-> (APlus (AId X) (ANum 1))]}} ->
  {{P}} LOOP X TO a2 DO c END {{fun st => P st /\ st X > aeval st a2}}.
Proof.
  intros P X c a Hhoare st st' He HP.
  remember (LOOP X TO a DO c END) as wcom eqn:Heqlcom.
  induction He;
  try (inversion Heqlcom); subst; clear Heqlcom.
  + split.
     assumption. assumption.
  + apply IHHe2. reflexivity.
     apply (Hhoare st st').
     - assumption.
     - split. assumption. assumption. 
Qed.

(* ********************************************** *)
(* Problem 3 *)
(* ********************************************** *)

(* Types *)

Inductive ty : Type := 
  | TBool  : ty 
  | TArrow : ty -> ty -> ty
  | TTsil : ty -> ty.

(* Terms *)

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm
  | tlin : tm
  | tsnoc : tm -> tm -> tm
  | tcase : tm -> tm -> id -> id -> tm -> tm. 

(* Values *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  | v_true : 
      value ttrue
  | v_false : 
      value tfalse
  | v_lin:
      value tlin
   | v_snoc: forall vs v,
       value vs -> value v -> value (tsnoc vs v).

Hint Constructors value.

(* Substitution *)

Reserved Notation "'[' x ':=' s ']' t" (at level 20, right associativity).

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' => 
      if beq_id x x' then s else t
  | tabs x' T t1 => 
      tabs x' T (if beq_id x x' then t1 else ([x:=s] t1)) 
  | tapp t1 t2 => 
      tapp ([x:=s] t1) ([x:=s] t2)
  | ttrue => 
      ttrue
  | tfalse => 
      tfalse
  | tif t1 t2 t3 => 
      tif ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
   | tlin => tlin
   | tsnoc t1 t2 =>
       tsnoc ([x:=s] t1) ([x:=s] t2)
   | tcase t1 t2 ys y t3 =>
       tcase ([x:=s] t1) ([x:=s] t2) ys y
         (if (beq_id x y) then t3 else 
           if (beq_id x ys) then t3 else ([x:=s] t3))
  end

where "'[' x ':=' s ']' t" := (subst x s t).

(* Evaluation relation *)

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         tapp t1 t2 ==> tapp t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' -> 
         tapp v1 t2 ==> tapp v1  t2'
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
    | ST_Snoc1 : forall t1 t1' t2,
      t1 ==> t1' ->
      tsnoc t1 t2 ==> tsnoc t1' t2
  | ST_Snoc2 : forall v1 t2 t2',
      value v1 ->
      t2 ==> t2' ->
      tsnoc v1 t2 ==> tsnoc v1 t2'
  | ST_TCase : forall t1 t1' t2 xs x t3,
      t1 ==> t1' ->
      tcase t1 t2 xs x t3 ==> tcase t1' t2 xs x t3
  | ST_TCaseLin : forall t2 xs x t3,
     tcase tlin t2 xs x t3 ==> t2
  | ST_TCaseSnoc : forall v1 v2 t2 xs x t3,
     tcase (tsnoc v1 v2) t2 xs x t3 ==> [xs:=v1] [x:=v2]t3
where "t1 '==>' t2" := (step t1 t2).

Hint Constructors step.

Definition relation a := a -> a -> Prop.

Inductive multi {X:Type} (R: relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation "t1 '==>*' t2" := (multi step t1 t2) (at level 40).

(* Contexts *)

Definition context := partial_map ty.

(* Typing relation *)

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).
    
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      update Gamma x T11 |- t12 \in T12 -> 
      Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 -> 
      Gamma |- t2 \in T11 -> 
      Gamma |- tapp t1 t2 \in T12
  | T_True : forall Gamma,
       Gamma |- ttrue \in TBool
  | T_False : forall Gamma,
       Gamma |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in TBool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- tif t1 t2 t3 \in T
    | T_Lin : forall Gamma T,
       Gamma |- tlin \in TTsil T
  | T_Snoc : forall Gamma t1 t2 T,
       Gamma |- t1 \in TTsil T ->
       Gamma |- t2 \in T ->
       Gamma |- tsnoc t1 t2 \in TTsil T
  | T_TCase : forall Gamma t1 t2 x xs t3 T T',
       Gamma |- t1 \in TTsil T ->
       Gamma |- t2 \in T' ->
       update (update Gamma xs (TTsil T)) x T |- t3 \in T' ->
       Gamma |- tcase t1 t2 xs x t3 \in T'

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

(* Canonical Forms *)

Lemma cannonical_forms_bool : forall t,
  empty |- t \in TBool ->
  value t ->
  (t = ttrue) \/ (t = tfalse).
Proof.
  intros t HT HVal.
  inversion HVal; intros; subst; try inversion HT; auto.
Qed.

Lemma cannonical_forms_fun : forall t T1 T2,
  empty |- t \in (TArrow T1 T2) ->
  value t ->
  exists x u, t = tabs x T1 u.
Proof.
  intros t T1 T2 HT HVal.
  inversion HVal; intros; subst; try inversion HT; subst; auto.
  exists x. exists t0.  auto.
Qed.

Lemma cannonical_forms_tsil : forall t T,
  empty |- t \in TTsil T ->
  value t ->
  t = tlin \/ (exists vs v, value vs /\ value v /\ t = tsnoc vs v).
Proof.
  intros t T HT HVal.
  inversion HVal; intros; subst; try inversion HT; subst; auto.
  -right. exists vs. exists v.  auto.
Qed.
(* Progress, by induction on type derivation *)

Theorem progress : forall t T, 
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.

Proof with eauto.
  intros t T Ht.
  remember (@empty ty) as Gamma.
  induction Ht; subst Gamma...
  + (* Case "T_Var" *)
    (* contradictory: variables cannot be typed in an 
       empty context *)
    inversion H. 

  + (* Case "T_App" *) 
    (* [t] = [t1 t2].  Proceed by cases on whether [t1] is a 
       value or steps... *)
    right. destruct IHHt1...
    - (* t1 is a value *)
      destruct IHHt2...
      * (* t2 is also a value *)
        assert (exists x0 t0, t1 = tabs x0 T11 t0).
        eapply cannonical_forms_fun; eauto.
        destruct H1 as [x0 [t0 Heq]]. subst.
        exists ([x0:=t2]t0)...

      * (* t2 steps *)
        inversion H0 as [t2' Hstp]. exists (tapp t1 t2')...

    - (* t1 steps *)
      inversion H as [t1' Hstp]. exists (tapp t1' t2)...

  + (* Case "T_If" *)
    right. destruct IHHt1...
    
    - (* t1 is a value *)
      destruct (cannonical_forms_bool t1); subst; eauto.

    - (* t1 also steps *)
      inversion H as [t1' Hstp]. exists (tif t1' t2 t3)...
  + destruct IHHt1...
      - destruct IHHt2. reflexivity.
        left...
        right. inversion H0 as [t2' Hstep2]. exists (tsnoc t1 t2')...
      - right. inversion H as [t1' Hstep1]. exists (tsnoc t1' t2)...
   + right. destruct IHHt1...
      - eapply cannonical_forms_tsil in H; eauto. destruct H; subst.
         exists t2. eauto.
         inversion H as [vs [v [Hvs [Hv Hsnoc]]]]. subst.
         exists ([xs:=vs] [x:=v] t3). eauto.
     - destruct H as [t1' Hstep]. exists (tcase t1' t2 xs x t3). eauto.  
Qed.


