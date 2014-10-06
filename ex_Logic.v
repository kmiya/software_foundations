(** * Logic: Logic in Coq *)

Require Export MoreCoq.

(** * Proofs and Evidence *)

(** ** Implications _are_ functions *)

(** * Conjunction (Logical "and") *)

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q) : type_scope.

(** ** "Eliminating" conjunctions *)

Theorem proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HP.  Qed.

(** **** Exercise: 1 star, optional (proj2) *)
Theorem proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply H.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  (* WORKED IN CLASS *)
  intros P Q H.
  inversion H as [HP HQ].
  split.
    Case "left". apply HQ.
    Case "right". apply HP.  Qed.


(** **** Exercise: 2 stars (and_assoc) *)
(** In the following proof, notice how the _nested pattern_ in the
    [inversion] breaks the hypothesis [H : P /\ (Q /\ R)] down into
    [HP: P], [HQ : Q], and [HR : R].  Finish the proof from there: *)

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  split.
    split.
      apply HP.
      apply HQ.
    apply HR.
Qed.

(** * Iff *)

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

Theorem iff_implies : forall P Q : Prop,
  (P <-> Q) -> P -> Q.
Proof.
  intros P Q H.
  inversion H as [HAB HBA]. apply HAB.  Qed.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q H.
  inversion H as [HAB HBA].
  split.
    Case "->". apply HBA.
    Case "<-". apply HAB.  Qed.

(** **** Exercise: 1 star, optional (iff_properties) *)
(** Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros P.
  split.
    intros HP. apply HP.
    intros HP. apply HP.
Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R HPQ HQR.
  inversion HPQ as [HAB HBA].
  inversion HQR as [HBC HCB].
  split.
    Case "P -> R".
      intros HP.
      apply HAB in HP. apply HBC. apply HP.
    Case "R -> P".
      intros HR.
      apply HCB in HR. apply HBA. apply HR.
Qed.
(** Hint: If you have an iff hypothesis in the context, you can use
    [inversion] to break it into two separate implications.  (Think
    about why this works.) *)

(** * Disjunction (Logical "or") *)

(** ** Implementing Disjunction *)

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "left". apply or_intror. apply HP.
    Case "right". apply or_introl. apply HQ.  Qed.

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. intros H. inversion H as [HP | [HQ HR]].
    Case "left". split.
      SCase "left". left. apply HP.
      SCase "right". left. apply HP.
    Case "right". split.
      SCase "left". right. apply HQ.
      SCase "right". right. apply HR.  Qed.

(** **** Exercise: 2 stars (or_distributes_over_and_2) *)
Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R H.
  inversion H as [[HP1 | HQ] [HP2 | HR]].
  Case "P1 and P2".
    left. apply HP1.
  Case "P1 and R".
    left. apply HP1.
  Case "Q and P2".
    left. apply HP2.
  Case "Q and R".
    right. split. apply HQ. apply HR.
Qed.

(** **** Exercise: 1 star, optional (or_distributes_over_and) *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
    Case "->". apply or_distributes_over_and_1.
    Case "<-". apply or_distributes_over_and_2.
Qed.

(** ** Relating [/\] and [\/] with [andb] and [orb] (advanced) *)

Theorem andb_prop : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  destruct b.
    Case "b = true". destruct c.
      SCase "c = true". apply conj. reflexivity. reflexivity.
      SCase "c = false". inversion H.
    Case "b = false". inversion H.  Qed.

Theorem andb_true_intro : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  inversion H.
  rewrite H0. rewrite H1. reflexivity. Qed.

(** **** Exercise: 2 stars, optional (bool_prop) *)
Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof.
  intros b c H. destruct b.
    Case "b = true". destruct c.
      SCase "c = true". inversion H.
      SCase "c = false". right. reflexivity.
    Case "b = false". left. reflexivity.
Qed.

Theorem orb_prop : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros b c H. destruct b.
    Case "b = true". left. reflexivity.
    Case "b = false". destruct c.
      SCase "c = true". right. reflexivity.
      SCase "c = false". inversion H.
Qed.

Theorem orb_false_elim : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof.
  intros b c H. destruct b.
    Case "b = true". inversion H.
    Case "b = false". destruct c.
      inversion H.
      apply conj. reflexivity. reflexivity.
Qed.

(** * Falsehood *)

Inductive False : Prop := .

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  inversion contra.  Qed.

(** ** Truth *)

(** **** Exercise: 2 stars, advanced (True) *)
(** Define [True] as another inductively defined proposition.  (The
    intuition is that [True] should be a proposition for which it is
    trivial to give evidence.) *)

Inductive True : Prop := true : True.

(** * Negation *)

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. inversion H.  Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q H. inversion H as [HP HNA]. unfold not in HNA.
  apply HNA in HP. inversion HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H.  Qed.

(** **** Exercise: 2 stars, advanced (double_neg_inf) *)
(** Write an informal proof of [double_neg]:

   _Theorem_: [P] implies [~~P], for any proposition [P].

   _Proof_:
(* TODO *)
   []
*)

(** **** Exercise: 2 stars (contrapositive) *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H1 H2. unfold not. unfold not in H2. intros H.
  apply H2. apply H1. apply H.
Qed.

(** **** Exercise: 1 star (not_both_true_and_false) *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P. unfold not. intros H. inversion H. apply H1. apply H0.
Qed.

(** **** Exercise: 1 star, advanced (informal_not_PNP) *)
(** Write an informal proof (in English) of the proposition [forall P
    : Prop, ~(P /\ ~P)]. *)

(* TODO *)
(** [] *)

(** *** Constructive logic *)

(** **** Exercise: 5 stars, advanced, optional (classical_axioms) *)
(** For those who like a challenge, here is an exercise
    taken from the Coq'Art book (p. 123).  The following five
    statements are often considered as characterizations of
    classical logic (as opposed to constructive logic, which is
    what is "built in" to Coq).  We can't prove them in Coq, but
    we can consistently add any one of them as an unproven axiom
    if we wish to work in classical logic.  Prove that these five
    propositions are equivalent. *)

Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.
Definition classic := forall P:Prop,
  ~~P -> P.
Definition excluded_middle := forall P:Prop,
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).

Module ex_classical_axioms.

(* Theorem th1eq2 : forall P Q : Prop, *)
(*   ((P->Q)->P)->P <-> ~~P -> P. *)
(* Proof. *)
(*   intros P Q. split. *)
(*   Case "->". intros H0. unfold not. intros H1. apply H0. *)
(*   intros H2. apply contrapositive in H2. unfold not in H2. *)
(*   apply H1 in H2. inversion H2. *)
(*   unfold not. intros HQ. apply H1. intros HP. apply double_neg.  *)
(** [] *)

End ex_classical_axioms.

(** **** Exercise: 3 stars (excluded_middle_irrefutable) *)
(** This theorem implies that it is always safe to add a decidability
axiom (i.e. an instance of excluded middle) for any _particular_ Prop [P].
Why? Because we cannot prove the negation of such an axiom; if we could,
we would have both [~ (P \/ ~P)] and [~ ~ (P \/ ~P)], a contradiction. *)

Theorem excluded_middle_irrefutable : forall (P : Prop),
  ~ ~ (P \/ ~ P).
Proof.
  intros P. unfold not. intros H0. apply H0.
  right. intros HP. apply H0. left. apply HP.
Qed.
