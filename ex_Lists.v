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
  | nil => l2
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
                   | false => oddmembers t
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

(** * Reasoning About Lists *)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n l'".
    reflexivity.  Qed.

(** ** Micro-Sermon *)

(** ** Induction on Lists *)

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons n l1'".
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** *** Informal version *)

(** *** Another example *)

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons".
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** *** Reversing a list *)

Fixpoint snoc (l:natlist) (v:nat) : natlist :=
  match l with
  | nil    => [v]
  | h :: t => h :: (snoc t v)
  end.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => snoc (rev t) h
  end.

(** *** Proofs about reverse *)

Theorem length_snoc : forall n : nat, forall l : natlist,
  length (snoc l n) = S (length l).
Proof.
  intros n l. induction l as [| n' l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n' l'".
    simpl. rewrite -> IHl'. reflexivity.  Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> length_snoc.
    rewrite -> IHl'. reflexivity.  Qed.

(** ** List Exercises, Part 1 *)

(** **** Exercise: 3 stars (list_exercises) *)
(** More practice with lists. *)

Theorem app_nil_end : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l. induction l as [| x xs].
  Case "l = []". reflexivity.
  Case "l = cons".
    simpl. rewrite -> IHxs. reflexivity. Qed.

Theorem rev_snoc : forall (v : nat) (l : natlist),
  rev (snoc l v) = v :: rev l.
Proof.
  intros v l. induction l as [| x xs].
  Case "l = []".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> IHxs. reflexivity. Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l. induction l as [| x xs].
  Case "l = []". reflexivity.
  Case "l = cons".
    simpl. rewrite -> rev_snoc. rewrite -> IHxs. reflexivity. Qed.

(* ref: https://github.com/etosch/software_foundations/blob/master/lesson3_Lists.v *)

(** There is a short solution to the next exercise.  If you find
    yourself getting tangled up, step back and try to look for a
    simpler way. *)

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  replace ((l1 ++ l2) ++ l3) with (l1 ++ l2 ++ l3).
  rewrite -> app_assoc.
  rewrite -> app_assoc. reflexivity.
  Case "replace".
    rewrite -> app_assoc. reflexivity. Qed.

Theorem snoc_append : forall (l : natlist) (n : nat),
  snoc l n = l ++ [n].
Proof.
  intros l n. induction l as [| x xs].
  Case "l = []".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> IHxs. reflexivity. Qed.

Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros l1 l2. induction l1 as [| x xs].
  Case "l1 = []".
    simpl. rewrite -> app_nil_end. reflexivity.
  Case "l1 = cons".
    simpl. rewrite -> IHxs.
    rewrite -> snoc_append. rewrite -> snoc_append.
    rewrite -> app_assoc. reflexivity. Qed.

(** An exercise about your implementation of [nonzeros]: *)

Lemma nonzeros_nil : forall l : natlist,
  nonzeros [] = [].
Proof.
  reflexivity. Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1 as [| x xs].
  Case "l1 = []".
    reflexivity.
  Case "l1 = cons".
    destruct x as [| x'].
    SCase "x = 0".
      simpl. rewrite -> IHxs. reflexivity.
    SCase "x > 0".
      simpl. rewrite -> IHxs. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars (beq_natlist) *)
(** Fill in the definition of [beq_natlist], which compares
    lists of numbers for equality.  Prove that [beq_natlist l l]
    yields [true] for every list [l]. *)

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1 with
    | nil => match l2 with
               | nil => true
               | _   => false
             end
    | h :: t => match l2 with
               | nil => false
               | h2 :: t2 => match beq_nat h h2 with
                               | false => false
                               | true  => beq_natlist t t2
                             end
                end
  end.

Example test_beq_natlist1 :   (beq_natlist nil nil = true).
Proof. reflexivity. Qed.
Example test_beq_natlist2 :   beq_natlist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example test_beq_natlist3 :   beq_natlist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Lemma beq_n_n : forall n : nat,
  beq_nat n n = true.
Proof.
  intros. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n > 0".
    simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem beq_natlist_refl : forall l : natlist,
  true = beq_natlist l l.
Proof.
  intro l. induction l as [| x xs].
  Case "l = []".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> beq_n_n.
    rewrite <- IHxs. reflexivity.
Qed.

(** ** List Exercises, Part 2 *)

(** **** Exercise: 2 stars (list_design) *)
(** Design exercise:
     - Write down a non-trivial theorem involving [cons]
       ([::]), [snoc], and [app] ([++]).
     - Prove it. *)

(* TODO *)
(** [] *)

(** **** Exercise: 3 stars, advanced (bag_proofs) *)
(** Here are a couple of little theorems to prove about your
    definitions about bags earlier in the file. *)

Theorem count_member_nonzero : forall (s : bag),
  ble_nat 1 (count 1 (1 :: s)) = true.
Proof.
  reflexivity.
Qed.

(** The following lemma about [ble_nat] might help you in the next proof. *)

Theorem ble_n_Sn : forall n,
  ble_nat n (S n) = true.
Proof.
  intros n. induction n as [| n'].
  Case "0".
    simpl.  reflexivity.
  Case "S n'".
    simpl. rewrite IHn'. reflexivity. Qed.

Theorem remove_decreases_count: forall (s : bag),
  ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros s. induction s as [| h t].
  Case "s = []".
    reflexivity.
  Case "s = cons".
    destruct h as [| h']. simpl.
    SCase "h = 0".
      rewrite -> ble_n_Sn. reflexivity.
    SCase "h > 0".
    simpl. rewrite -> IHt. reflexivity.
Qed.

(** **** Exercise: 3 stars, optional (bag_count_sum) *)
(** Write down an interesting theorem about bags involving the
    functions [count] and [sum], and prove it.*)

(* TODO *)
(** [] *)

(** **** Exercise: 4 stars, advanced (rev_injective) *)
(** Prove that the [rev] function is injective, that is,

    forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.

There is a hard way and an easy way to solve this exercise.
*)

Theorem rev_injective: forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 H.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.

(** * Options *)

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Fixpoint index (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None
  | a :: l' => match beq_nat n O with
               | true => Some a
               | false => index (pred n) l'
               end
  end.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(** **** Exercise: 2 stars (hd_opt) *)
(** Using the same idea, fix the [hd] function from earlier so we don't
   have to pass a default element for the [nil] case.  *)

Definition hd_opt (l : natlist) : natoption :=
  match l with
    | nil => None
    | h :: t => Some h
  end.

Example test_hd_opt1 : hd_opt [] = None.
Proof. reflexivity. Qed.

Example test_hd_opt2 : hd_opt [1] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_opt3 : hd_opt [5;6] = Some 5.
Proof. reflexivity. Qed.

(** **** Exercise: 1 star, optional (option_elim_hd) *)
(** This exercise relates your new [hd_opt] to the old [hd]. *)

Theorem option_elim_hd : forall (l : natlist) (default : nat),
  hd default l = option_elim default (hd_opt l).
Proof.
  intros l d. destruct l as [| h t].
  reflexivity.
  reflexivity.
Qed.

(** * Dictionaries *)

Module Dictionary.

Inductive dictionary : Type :=
  | empty  : dictionary
  | record : nat -> nat -> dictionary -> dictionary.

Definition insert (key value : nat) (d : dictionary) : dictionary :=
  (record key value d).

Fixpoint find (key : nat) (d : dictionary) : natoption :=
  match d with
  | empty         => None
  | record k v d' => if (beq_nat key k)
                       then (Some v)
                       else (find key d')
  end.

(** **** Exercise: 1 star (dictionary_invariant1) *)
(** Complete the following proof. *)

Theorem dictionary_invariant1' : forall (d : dictionary) (k v: nat),
  (find k (insert k v d)) = Some v.
Proof.
  intros d k v.
  simpl. rewrite <- beq_nat_refl. reflexivity.
Qed.

(** **** Exercise: 1 star (dictionary_invariant2) *)
(** Complete the following proof. *)

Theorem dictionary_invariant2' : forall (d : dictionary) (m n o: nat),
  beq_nat m n = false -> find m d = find m (insert n o d).
Proof.
  intros d m n o H.
  simpl. rewrite -> H. reflexivity.
Qed.

End Dictionary.

End NatList.
