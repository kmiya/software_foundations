(** * Introduction *)
(** ** Booleans *)

Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b:bool) : bool :=
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

(** **** Exercise: 1 star (nandb) *)
(** Complete the definition of the following function, then make
    sure that the [Example] assertions below can each be verified by
    Coq.  *)

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => negb b2
    | false => true
  end.

Example test_nandb1:               (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2:               (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3:               (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4:               (nandb true true) = false.
Proof. reflexivity. Qed.

(** **** Exercise: 1 star (andb3) *)
(** Do the same for the [andb3] function below. This function should
    return [true] when all of its inputs are [true], and [false]
    otherwise. *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
    | true => andb b2 b3
    | false => false
  end.

Example test_andb31:                 (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32:                 (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33:                 (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34:                 (andb3 true true false) = false.
Proof. reflexivity. Qed.

(** ** Numbers *)

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool   :=   negb (evenb n).

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

(** **** Exercise: 1 star (factorial) *)
(** Recall the standard factorial function:
<<
    factorial(0)  =  1
    factorial(n)  =  n * factorial(n-1)     (if n>0)
>>
    Translate this into Coq. *)

Fixpoint factorial (n : nat) : nat :=
  match n with
    | O => 1
    | S n' => mult n (factorial n')
  end.

Example test_factorial1:          (factorial 3) = 6.
Proof. reflexivity. Qed.
Example test_factorial2:          (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

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

(** **** Exercise: 2 stars (blt_nat) *)
(** The [blt_nat] function tests [nat]ural numbers for [l]ess-[t]han,
    yielding a [b]oolean.  Instead of making up a new [Fixpoint] for
    this one, define it in terms of a previously defined function.

    Note: If you have trouble with the [simpl] tactic, try using
    [compute], which is like [simpl] on steroids.  However, there is a
    simple, elegant solution for which [simpl] suffices. *)

Definition blt_nat (n m : nat) : bool :=
  match n with
    | O => ble_nat (S O) m
    | n' => ble_nat (S n') m
  end.

Example test_blt_nat1:             (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2:             (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3:             (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

(** * Proof by Simplification *)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity.  Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity.  Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity.  Qed.

(** * Proof by Rewriting *)

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.

Proof.
  intros n m.   (* move both quantifiers into the context *)
  intros H.     (* move the hypothesis into the context *)
  rewrite <- H. (* Rewrite the goal using the hypothesis *)
  reflexivity.  Qed.

(** **** Exercise: 1 star (plus_id_exercise) *)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  rewrite -> H1.
  intros H2.
  rewrite -> H2.
  reflexivity. Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.  Qed.

(** **** Exercise: 2 stars (mult_S_1) *)
Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity. Qed.

(** * Proof by Case Analysis *)

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
    reflexivity.
    reflexivity.  Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
    reflexivity.
    reflexivity.  Qed.

(** **** Exercise: 1 star (zero_nbeq_plus_1) *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n. destruct n as [|n'].
  reflexivity.
  reflexivity.  Qed.

(** * More Exercises *)

(** **** Exercise: 2 stars (boolean functions) *)
(** Use the tactics you have learned so far to prove the following
    theorem about boolean functions. *)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros.
  rewrite -> H.
  rewrite -> H.
  reflexivity. Qed.

(** Now state and prove a theorem [negation_fn_applied_twice] similar
    to the previous one but where the second hypothesis says that the
    function [f] has the property that [f x = negb x].*)

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros.
  rewrite -> H.
  rewrite -> H.
  rewrite -> negb_involutive.
  reflexivity. Qed.

(** **** Exercise: 2 stars (andb_eq_orb) *)
(** Prove the following theorem.  (You may want to first prove a
    subsidiary lemma or two. Alternatively, remember that you do
    not have to introduce all hypotheses at the same time.) *)

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c. destruct b. destruct c.
  simpl. reflexivity.
  simpl. intros H. rewrite -> H.
  reflexivity.
  simpl. intros H. rewrite -> H.
  reflexivity.
Qed.

(** **** Exercise: 3 stars (binary) *)
(** Consider a different, more efficient representation of natural
    numbers using a binary rather than unary system.  That is, instead
    of saying that each natural number is either zero or the successor
    of a natural number, we can say that each binary number is either

      - zero,
      - twice a binary number, or
      - one more than twice a binary number.

    (a) First, write an inductive definition of the type [bin]
        corresponding to this description of binary numbers.

    (Hint: Recall that the definition of [nat] from class,
    Inductive nat : Type :=
      | O : nat
      | S : nat -> nat.
    says nothing about what [O] and [S] "mean."  It just says "[O] is
    in the set called [nat], and if [n] is in the set then so is [S
    n]."  The interpretation of [O] as zero and [S] as successor/plus
    one comes from the way that we _use_ [nat] values, by writing
    functions to do things with them, proving things about them, and
    so on.  Your definition of [bin] should be correspondingly simple;
    it is the functions you will write next that will give it
    mathematical meaning.)

    (b) Next, write an increment function for binary numbers, and a
        function to convert binary numbers to unary numbers.

    (c) Write some unit tests for your increment and binary-to-unary
        functions. Notice that incrementing a binary number and
        then converting it to unary should yield the same result as first
        converting it to unary and then incrementing.
*)

(* TODO *)

(** * Optional Material *)

(** **** Exercise: 2 stars, optional (decreasing) *)
(** To get a concrete sense of this, find a way to write a sensible
    [Fixpoint] definition (of a simple function on numbers, say) that
    _does_ terminate on all inputs, but that Coq will _not_ accept
    because of this restriction. *)

(* TODO See https://github.com/etosch/software_foundations/blob/master/lesson1_Basics.v *)