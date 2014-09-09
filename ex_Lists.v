(** * Lists: Working with Structured Data *)

Require Export Induction.

Module NatList.

(* ###################################################### *)
(** * Pairs of Numbers *)

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.  destruct p as [n m].  simpl.  reflexivity.  Qed.

(** **** Exercise: 1 star (snd_fst_is_swap) *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

(** **** Exercise: 1 star, optional (fst_swap_is_snd) *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
intros p. destruct p as [n m]. simpl. reflexivity. Qed.

(** * Lists of Numbers *)

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(** *** Repeat *)

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

(** *** Length *)

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(** *** Append *)

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

(** **** Exercise: 2 stars (list_funs) *)
(** Complete the definitions of [nonzeros], [oddmembers] and
    [countoddmembers] below. Have a look at the tests to understand
    what these functions should do. *)

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
    | nil => nil
    | 0 :: t => nonzeros t
    | h :: t => h :: nonzeros t
  end.

Example test_nonzeros:            nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t =>  match oddb h with
                   | true  => h :: oddmembers t
                   | false  => oddmembers t
                 end
  end.

Example test_oddmembers:            oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Fixpoint countoddmembers (l:natlist) : nat :=
  length (oddmembers l).

Example test_countoddmembers1:    countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers2:    countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers3:    countoddmembers nil = 0.
Proof. reflexivity. Qed.

(** **** Exercise: 3 stars, advanced (alternate) *)
(** Complete the definition of [alternate], which "zips up" two lists
    into one, alternating between elements taken from the first list
    and elements from the second.  See the tests below for more
    specific examples.

    Note: one natural and elegant way of writing [alternate] will fail
    to satisfy Coq's requirement that all [Fixpoint] definitions be
    "obviously terminating."  If you find yourself in this rut, look
    for a slightly more verbose solution that considers elements of
    both lists at the same time.  (One possible solution requires
    defining a new kind of pairs, but this is not the only way.)  *)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
    | nil => l2
    | h :: s => match l2 with
                  | nil => l1
                  | x :: xs => h :: x :: alternate s xs
                end
  end.

Example test_alternate1:        alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.
Example test_alternate2:        alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.
Example test_alternate3:        alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.
Example test_alternate4:        alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.

(** ** Bags via Lists *)

Definition bag := natlist.

(** **** Exercise: 3 stars (bag_functions) *)
(** Complete the following definitions for the functions
    [count], [sum], [add], and [member] for bags. *)

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
    | nil => 0
    | x :: xs => match (beq_nat x v) with
                  | true  => S (count v xs)
                  | false => count v xs
                 end
  end.

(** All these proofs can be done just by [reflexivity]. *)

Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.
Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

(** Multiset [sum] is similar to set [union]: [sum a b] contains
    all the elements of [a] and of [b].  (Mathematicians usually
    define [union] on multisets a little bit differently, which
    is why we don't use that name for this operation.)
    For [sum] we're giving you a header that does not give explicit
    names to the arguments.  Moreover, it uses the keyword
    [Definition] instead of [Fixpoint], so even if you had names for
    the arguments, you wouldn't be able to process them recursively.
    The point of stating the question this way is to encourage you to
    think about whether [sum] can be implemented in another way --
    perhaps by using functions that have already been defined.  *)

Definition sum : bag -> bag -> bag := app.
Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag :=
  match s with
    | nil => [v]
    | x :: xs => v :: s
  end.

Example test_add1:                count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2:                count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool :=
  ble_nat 1 (count v s).

Example test_member1:             member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2:             member 2 [1;4;1] = false.
Proof. reflexivity. Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (bag_more_functions) *)
(** Here are some more bag functions for you to practice with. *)

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
    | nil => nil
    | x :: xs => match beq_nat v x with
                   | true  => xs
                   | false => x :: remove_one v xs
                 end
end.

Example test_remove_one1:         count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2:         count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3:         count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_one4:         count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
    | nil => nil
    | x :: xs => match beq_nat v x with
                   | true  => remove_all v xs
                   | false => x :: remove_all v xs
                 end
end.

Example test_remove_all1:          count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2:          count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3:          count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4:          count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
    | nil => true
    | x :: xs => match member x s2 with
                   | true  => subset xs (remove_one x s2)
                   | false => false
                 end
  end.

Example test_subset1:              subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_subset2:              subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.
(** [] *)

(** **** Exercise: 3 stars (bag_theorem) *)
(** Write down an interesting theorem about bags involving the
    functions [count] and [add], and prove it.  Note that, since this
    problem is somewhat open-ended, it's possible that you may come up
    with a theorem which is true, but whose proof requires techniques
    you haven't learned yet.  Feel free to ask for help if you get
    stuck! *)
(* TODO *)
(* Fact a_great_theorem : forall a b : nat, forall s : bag, *)
(*   beq_nat a b = true -> count b (add a s) = 1 + count b s. *)
(* Proof. Abort. *)
(** [] *)
