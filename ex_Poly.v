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

(** ** Polymorphic Pairs *)

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with (x,y) => x end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with (x,y) => y end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match (lx,ly) with
  | ([],_) => []
  | (_,[]) => []
  | (x::tx, y::ty) => (x,y) :: (combine tx ty)
  end.

(** **** Exercise: 1 star, optional (combine_checks) *)
(** Try answering the following questions on paper and
    checking your answers in coq:
    - What is the type of [combine] (i.e., what does [Check
      @combine] print?)

     => list X -> list Y -> list (X*Y)

    - What does
        Eval compute in (combine [1;2] [false;false;true;true]).
      print?

     => [(1,false); (2,false)]

   []
*)
Check @combine.
(* =>  forall X Y : Type, list X -> list Y -> list (X * Y) *)
Eval compute in (combine [1;2] [false;false;true;true]).
(*  = [(1, false); (2, false)]  *)
(*  : list (nat * bool)         *)


(** **** Exercise: 2 stars (split) *)
(** The function [split] is the right inverse of combine: it takes a
    list of pairs and returns a pair of lists.  In many functional
    programing languages, this function is called [unzip].

    Uncomment the material below and fill in the definition of
    [split].  Make sure it passes the given unit tests. *)

Fixpoint split
           {X Y : Type} (l : list (X*Y))
           : (list X) * (list Y) :=
  match l with
    | [] => ([],[])
    | h :: t => match h with
                  | (x,y) => (x :: fst (split t), y :: snd (split t))
                end
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

(** ** Polymorphic Options *)

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

(** **** Exercise: 1 star, optional (hd_opt_poly) *)
(** Complete the definition of a polymorphic version of the
    [hd_opt] function from the last chapter. Be sure that it
    passes the unit tests below. *)

Definition hd_opt {X : Type} (l : list X)  : option X :=
  match l with
    | [] => None
    | h :: t => Some h
  end.

(** Once again, to force the implicit arguments to be explicit,
    we can use [@] before the name of the function. *)

Check @hd_opt.

Example test_hd_opt1 :  hd_opt [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_opt2 :   hd_opt  [[1];[2]]  = Some [1].
Proof. reflexivity. Qed.

(** * Functions as Data *)
(** ** Higher-Order Functions *)

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

(** ** Partial Application *)

Definition plus3 := plus 3.

(** ** Digression: Currying *)

(** **** Exercise: 2 stars, advanced (currying) *)
(** In Coq, a function [f : A -> B -> C] really has the type [A
    -> (B -> C)].  That is, if you give [f] a value of type [A], it
    will give you function [f' : B -> C].  If you then give [f'] a
    value of type [B], it will return a value of type [C].  This
    allows for partial application, as in [plus3].  Processing a list
    of arguments with functions that return functions is called
    _currying_, in honor of the logician Haskell Curry.

    Conversely, we can reinterpret the type [A -> B -> C] as [(A *
    B) -> C].  This is called _uncurrying_.  With an uncurried binary
    function, both arguments must be given at once as a pair; there is
    no partial application. *)

(** We can define currying as follows: *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(** As an exercise, define its inverse, [prod_uncurry].  Then prove
    the theorems below to show that the two are inverses. *)

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
  match p with (x,y) => f x y end.

(** (Thought exercise: before running these commands, can you
    calculate the types of [prod_curry] and [prod_uncurry]?) *)

Check @prod_curry.    (* forall X Y Z : Type, (X * Y -> Z) -> X -> Y -> Z *)
Check @prod_uncurry.  (* forall X Y Z : Type, (X -> Y -> Z) -> X * Y -> Z *)

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y. reflexivity. Qed.

Theorem curry_uncurry : forall (X Y Z : Type)
                               (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p. destruct p as [n m].
  reflexivity.
Qed.

(** ** Filter *)

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

(** ** Anonymous Functions *)

(** **** Exercise: 2 stars (filter_even_gt7) *)

(** Use [filter] (instead of [Fixpoint]) to write a Coq function
    [filter_even_gt7] that takes a list of natural numbers as input
    and returns a list of just those that are even and greater than
    7. *)

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun x => andb (evenb x) (negb (blt_nat x 7))) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8;7] = [10;12;8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

(** **** Exercise: 3 stars (partition) *)
(** Use [filter] to write a Coq function [partition]:
  partition : forall X : Type,
              (X -> bool) -> list X -> list X * list X
   Given a set [X], a test function of type [X -> bool] and a [list
   X], [partition] should return a pair of lists.  The first member of
   the pair is the sublist of the original list containing the
   elements that satisfy the test, and the second is the sublist
   containing those that fail the test.  The order of elements in the
   two sublists should be the same as their order in the original
   list.
*)

Definition partition {X : Type} (test : X -> bool) (l : list X)
                     : list X * list X :=
  ( (filter (fun x => test x) l), (filter (fun x => negb (test x)) l) ).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

(** ** Map *)

Fixpoint map {X Y:Type} (f:X->Y) (l:list X)
             : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

(** ** Map for options *)
(** **** Exercise: 3 stars (map_rev) *)
(** Show that [map] and [rev] commute.  You may need to define an
    auxiliary lemma. *)

Lemma map_snoc : forall (X Y : Type) (f : X -> Y) (l : list X) (v : X),
  map f (snoc l v) = snoc (map f l) (f v).
Proof.
  intros X Y f l v. induction l as [| h t].
  Case "l = []".
    reflexivity.
  Case "l = cons".
    simpl. rewrite IHt. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l. induction l as [| h t].
  Case "l = []".
    reflexivity.
  Case "l = cons".
    simpl. rewrite <- IHt. rewrite map_snoc. reflexivity.
Qed.

(** **** Exercise: 2 stars (flat_map) *)
(** The function [map] maps a [list X] to a [list Y] using a function
    of type [X -> Y].  We can define a similar function, [flat_map],
    which maps a [list X] to a [list Y] using a function [f] of type
    [X -> list Y].  Your definition should work by 'flattening' the
    results of [f], like so:
        flat_map (fun n => [n;n+1;n+2]) [1;5;10]
      = [1; 2; 3; 5; 6; 7; 10; 11; 12].
*)

Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l : list X)
                   : (list Y) :=
  match l with
    | []     => []
    | h :: t => app (f h) (flat_map f t)
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None   => None
    | Some x => Some (f x)
  end.

(** **** Exercise: 2 stars, optional (implicit_args) *)
(** The definitions and uses of [filter] and [map] use implicit
    arguments in many places.  Replace the curly braces around the
    implicit arguments with parentheses, and then fill in explicit
    type parameters where necessary and use Coq to check that you've
    done so correctly.  (This exercise is not to be turned in; it is
    probably easiest to do it on a _copy_ of this file that you can
    throw away afterwards.)  [] *)

Module Ex_implicit_args.

Fixpoint map_explicit (X Y : Type) (f : X->Y) (l : list X)
             : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map_explicit X Y f t)
  end.

Fixpoint filter_explicit (X:Type) (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter_explicit X test t)
                        else       filter_explicit X test t
  end.

End Ex_implicit_args.

(** ** Fold *)

Fixpoint fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(** **** Exercise: 1 star, advanced (fold_types_different) *)
(** Observe that the type of [fold] is parameterized by _two_ type
    variables, [X] and [Y], and the parameter [f] is a binary operator
    that takes an [X] and a [Y] and returns a [Y].  Can you think of a
    situation where it would be useful for [X] and [Y] to be
    different? *)

(* For example, let X be nam and Y be bool. The setting is useful for detecting some exceptional numbers. *)


(** ** Functions For Constructing Functions *)

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Definition override {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if beq_nat k k' then x else f k'.

Definition fmostlytrue := override (override ftrue 1 false) 3 false.

(** **** Exercise: 1 star (override_example) *)
(** Before starting to work on the following proof, make sure you
    understand exactly what the theorem is saying and can paraphrase
    it in your own words.  The proof itself is straightforward. *)

Theorem override_example : forall (b:bool),
  (override (constfun b) 3 true) 2 = b.
Proof.
  intros b. reflexivity. Qed.
(* The input 2 is not equal to 3, so the override returns (constfun b) 2.
   It's just b by definition of constfun. *)
(** [] *)


(** * The [unfold] Tactic *)

Theorem override_eq : forall {X:Type} x k (f:nat->X),
  (override f k x) k = x.
Proof.
  intros X x k f.
  unfold override.
  rewrite <- beq_nat_refl.
  reflexivity.  Qed.

(** **** Exercise: 2 stars (override_neq) *)
Theorem override_neq : forall (X : Type) x1 x2 k1 k2 (f : nat -> X),
  f k1 = x1 ->
  beq_nat k2 k1 = false ->
  (override f k2 x2) k1 = x1.
Proof.
  intros X x1 x2 k1 k2 f H1 H2.
  unfold override.
  rewrite H2.
  rewrite H1. reflexivity.
Qed.


(** * Additional Exercises *)

(** **** Exercise: 2 stars (fold_length) *)
(** Many common functions on lists can be implemented in terms of
   [fold].  For example, here is an alternative definition of [length]: *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

(** Prove the correctness of [fold_length]. *)

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X l.
  unfold fold_length.
  induction l as [| h t].
  Case "l = []".
    reflexivity.
  Case "l = cons".
    simpl. rewrite IHt. reflexivity.
Qed.

(** **** Exercise: 3 stars (fold_map) *)
(** We can also define [map] in terms of [fold].  Finish [fold_map]
    below. *)

Definition fold_map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun a l' => f a :: l') l [].

(** Write down a theorem in Coq stating that [fold_map] is correct,
    and prove it. *)

Theorem fold_map_correct : forall (X Y : Type) (f : X -> Y) (l : list X),
  fold_map f l = map f l.
Proof.
  intros X Y f l.
  unfold fold_map.
  induction l as [| h t].
  Case "l = []".
    reflexivity.
  Case "l = cons".
    simpl. rewrite IHt. reflexivity.
Qed.
