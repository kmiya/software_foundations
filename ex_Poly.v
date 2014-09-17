(** * Poly: Polymorphism and Higher-Order Functions *)

Require Export Lists.

(** * Polymorphism *)
(** ** Polymorphic Lists *)

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
  | nil      => 0
  | cons h t => S (length X t)
  end.

Fixpoint app (X : Type) (l1 l2 : list X)
                : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) :=
  match l with
  | nil      => cons X v (nil X)
  | cons h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X:Type) (l:list X) : list X :=
  match l with
  | nil      => nil X
  | cons h t => snoc X (rev X t) h
  end.

Module MumbleBaz.
(** **** Exercise: 2 stars (mumble_grumble) *)
(** Consider the following two inductively defined types. *)

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.
Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(** Which of the following are well-typed elements of [grumble X] for
    some type [X]?
      - [d (b a 5)]
      - [d mumble (b a 5)]
      - [d bool (b a 5)]
      - [e bool true]
      - [e mumble (b c 0)]
      - [e bool (b c 0)]
      - [c]
(* FILL IN HERE *)
[] *)
(* Check d (b a 5).             (* type error *) *)
Check d mumble (b a 5).         (* OK: grumble mumble  *)
Check d bool (b a 5).           (* OK: grumble bool *)
Check e bool true.              (* OK: grumble bool *)
Check e mumble (b c 0).         (* OK: grumble mumble *)
(* Check e bool (b c 0).        (* type error *) *)
Check c.                        (* mumble *)


(** **** Exercise: 2 stars (baz_num_elts) *)
(** Consider the following inductive definition: *)

Inductive baz : Type :=
   | x : baz -> baz
   | y : baz -> bool -> baz.

(** How _many_ elements does the type [baz] have?
(* Zero. See http://cs.stackexchange.com/questions/29365/baz-num-elts-exercise-from-software-foundations *)
[] *)

End MumbleBaz.

(** *** Type Annotation Inference *)

(** *** Type Argument Synthesis *)

(** *** Implicit Arguments *)

Arguments nil {X}.
Arguments cons {X} _ _.  (* use underscore for argument position that has no name *)
Arguments length {X} l.
Arguments app {X} l1 l2.
Arguments rev {X} l.
Arguments snoc {X} l v.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(** *** Exercises: Polymorphic Lists *)

(** **** Exercise: 2 stars, optional (poly_exercises) *)
(** Here are a few simple exercises, just like ones in the [Lists]
    chapter, for practice with polymorphism.  Fill in the definitions
    and complete the proofs below. *)

Fixpoint repeat {X : Type} (n : X) (count : nat) : list X :=
  match count with
    | 0 => []
    | S c' => cons n (repeat n c')
  end.

Example test_repeat1:
  repeat true 2 = cons true (cons true nil).
Proof. reflexivity. Qed.

Theorem nil_app : forall X : Type, forall l : list X,
  app [] l = l.
Proof.
  intros X l. reflexivity. Qed.

Theorem rev_snoc : forall X : Type,
                     forall v : X,
                     forall s : list X,
  rev (snoc s v) = v :: (rev s).
Proof.
  intros X v s. induction s as [| h t].
  Case "s = []".
    reflexivity.
  Case "s = cons".
    simpl. rewrite -> IHt. reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l. induction l as [| h t].
  Case "l = []".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> rev_snoc.
    rewrite -> IHt. reflexivity.
Qed.

Theorem snoc_with_append : forall X : Type,
                         forall l1 l2 : list X,
                         forall v : X,
  snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  intros X l1 l2 v. induction l1 as [| h t].
  Case "l1 = []".
    reflexivity.
  Case "l1 = cons".
    simpl. rewrite -> IHt. reflexivity.
Qed.
