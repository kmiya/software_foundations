Require Export Poly.

(** * The [apply] Tactic *)

(** **** Exercise: 2 stars, optional (silly_ex) *)
(** Complete the following proof without using [simpl]. *)

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  intros eq1 eq2.
  apply eq2.
Qed.

(** **** Exercise: 3 stars (apply_exercise1) *)
(** Hint: you can use [apply] with previously defined lemmas, not
    just hypotheses in the context.  Remember that [SearchAbout] is
    your friend. *)

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l' e1.
  rewrite -> e1.
  symmetry.
  apply rev_involutive.
Qed.

(** **** Exercise: 1 star, optional (apply_rewrite) *)
(** Briefly explain the difference between the tactics [apply] and
    [rewrite].  Are there situations where both can usefully be
    applied?
  (* The above answer of the last exercise is a situation where both can usefully be applied. *)
*)

(** * The [apply ... with ...] Tactic *)

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity.  Qed.

(** **** Exercise: 3 stars, optional (apply_with_exercise) *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p e1 e2.
  apply trans_eq with m. apply e2. apply e1. Qed.

(** * The [inversion] tactic *)

Theorem eq_add_S : forall (n m : nat),
     S n = S m ->
     n = m.
Proof.
  intros n m eq. inversion eq. reflexivity.  Qed.

(** **** Exercise: 1 star (sillyex1) *)
Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  intros X x y z l j e1 e2.
  inversion e2. reflexivity. Qed.
(** [] *)

(** **** Exercise: 1 star (sillyex2) *)
Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof.
  intros X x y z l j eq1 eq2.
  inversion eq1. Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
    x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq.  reflexivity.  Qed.

(** **** Exercise: 2 stars, optional (practice) *)
(** A couple more nontrivial but not-too-complicated proofs to work
    together in class, or for you to work as exercises. *)

Theorem beq_nat_0_l : forall n,
   beq_nat 0 n = true -> n = 0.
Proof.
  intros n eq. destruct n.
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    inversion eq.
Qed.

Theorem beq_nat_0_r : forall n,
   beq_nat n 0 = true -> n = 0.
Proof.
  intros n eq. destruct n.
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    inversion eq.
  Qed.

(** * Using Tactics on Hypotheses *)

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b  ->
     beq_nat n m = b.
Proof.
  intros n m b H. simpl in H. apply H.  Qed.

(** **** Exercise: 3 stars (plus_n_n_injective) *)
(** Practice using "in" variants in this exercise. *)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
    (* Hint: use the plus_n_Sm lemma *)
  Case "n = 0".
    intros m. destruct m as [| m'].
    SCase "m = 0".
      reflexivity.
    SCase "m = S m'".
      intros eq.
      inversion eq.
  Case "n = S n'".
    intros m. destruct m as [| m'].
    SCase "m = 0".
      intros eq. inversion eq.
    SCase "m = S m'".
      intros eq.
      rewrite <- plus_n_Sm in eq.
      rewrite <- plus_n_Sm in eq.
      inversion eq.
      apply IHn' in H0.
      rewrite H0. reflexivity.
Qed.

(** * Varying the Induction Hypothesis *)

(** What went wrong? *)

Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = O". simpl. intros m eq. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion eq.
  Case "n = S n'".
    intros m eq.
    destruct m as [| m'].
    SCase "m = O".
      inversion eq.
    SCase "m = S m'".
      apply f_equal.
      apply IHn'. inversion eq. reflexivity. Qed.

(** The proof of this theorem (left as an exercise) has to be treated similarly: *)

(** **** Exercise: 2 stars (beq_nat_true) *)
Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    intros m eq. destruct m as [| m'].
    SCase "m = 0". reflexivity.
    SCase "m = S m'". inversion eq.
  Case "n = S n'".
    intros m eq. destruct m as [| m'].
    SCase "m = 0". inversion eq.
    SCase "m = S m'".
    apply f_equal.
    apply IHn'. inversion eq. reflexivity.
Qed.

(** **** Exercise: 2 stars, advanced (beq_nat_true_informal) *)
(** Give a careful informal proof of [beq_nat_true], being as explicit
    as possible about quantifiers. *)

(* TODO *)

(** **** Exercise: 3 stars (gen_dep_practice) *)

(** Prove this by induction on [l]. *)

Theorem index_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     index n l = None.
Proof.
  intros n X l. generalize dependent n.
  induction l as [| h t].
  Case "l = []". reflexivity.
  Case "l = cons".
    intros n eq. destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
    apply IHt. inversion eq. reflexivity. Qed.

(** **** Exercise: 3 stars, advanced, optional (index_after_last_informal) *)
(** Write an informal proof corresponding to your Coq proof
    of [index_after_last]:

     _Theorem_: For all sets [X], lists [l : list X], and numbers
      [n], if [length l = n] then [index n l = None].

     _Proof_:
     (* TODO *)
[]
*)

(** **** Exercise: 3 stars, optional (gen_dep_practice_more) *)
(** Prove this by induction on [l]. *)

Theorem length_snoc''' : forall (n : nat) (X : Type)
                              (v : X) (l : list X),
     length l = n ->
     length (snoc l v) = S n.
Proof.
  intros n X v l. generalize dependent n.
  induction l as [| h t].
  Case "l = []".
    intros n eq. simpl. rewrite <- eq. reflexivity.
  Case "l = cons".
    intros n eq. destruct n as [| n'].
    SCase "n = 0".
      simpl. apply f_equal. inversion eq.
    SCase "n = S n'".
    simpl. apply f_equal. apply IHt.
    inversion eq. reflexivity.
Qed.

(** **** Exercise: 3 stars, optional (app_length_cons) *)
(** Prove this by induction on [l1], without using [app_length]. *)

Theorem app_length_cons : forall (X : Type) (l1 l2 : list X)
                                  (x : X) (n : nat),
     length (l1 ++ (x :: l2)) = n ->
     S (length (l1 ++ l2)) = n.
Proof.
  intros X l1. induction l1 as [| h t].
  Case "l1 = []".
    intros l2 x n eq. simpl. simpl in eq. apply eq.
  Case "l1 = cons".
    intros l2 x n. generalize dependent x. destruct n as [| n'].
    intros x eq.
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      intros x' eq. apply f_equal. apply IHt with x'.
      inversion eq. reflexivity.
Qed.

(** **** Exercise: 4 stars, optional (app_length_twice) *)
(** Prove this by induction on [l], without using app_length. *)

(* ref: http://lpaste.net/6928329435871444992 *)
Lemma length_simp : forall (X : Type) (l1 l2 : list X) (v : X),
  length (l1 ++ v :: l2) = S (length (l1 ++ l2)).
Proof.
  intros X l1 l2 v. induction l1 as [| h t].
  Case "l1 = []". reflexivity.
  Case "l1 = cons".
    simpl. rewrite IHt. reflexivity.
Qed.

Theorem app_length_twice : forall (X:Type) (n:nat) (l:list X),
     length l = n ->
     length (l ++ l) = n + n.
Proof.
  intros X n l. generalize dependent n.
  induction l as [| h t].
  Case "l = []".
    intros n eq. simpl. rewrite <- eq. reflexivity.
  Case "l = cons".
    intros n eq. destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      simpl. rewrite length_simp. rewrite <- plus_n_Sm.
      apply f_equal. apply f_equal.
      apply IHt. inversion eq. reflexivity.
Qed.

(** **** Exercise: 3 stars, optional (double_induction) *)
(** Prove the following principle of induction over two naturals. *)

Theorem double_induction: forall (P : nat -> nat -> Prop),
  P 0 0 ->
  (forall m, P m 0 -> P (S m) 0) ->
  (forall n, P 0 n -> P 0 (S n)) ->
  (forall m n, P m n -> P (S m) (S n)) ->
  forall m n, P m n.
Proof.
  intros P e1 e2 e3 e4.
  intros m. induction m as [| m'].
  Case "m = 0". induction n as [| n'].
    SCase "n = 0". apply e1.
    SCase "n = S n'". apply e3. apply IHn'.
  Case "m = S m'". destruct n as [| n'].
    SCase "n = 0". apply e2. apply IHm'.
    SCase "n = S n'". apply e4. apply IHm'.
Qed.

(** * Using [destruct] on Compound Expressions *)

(** **** Exercise: 1 star (override_shadow) *)
Theorem override_shadow : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  intros X x1 x2 k1 k2 f. unfold override.
  destruct (beq_nat k1 k2).
    Case "beq_nat k1 k2 = true". reflexivity.
    Case "beq_nat k1 k2 = false". reflexivity.
Qed.

(** **** Exercise: 3 stars, optional (combine_split) *)
(** Complete the proof below *)

(* ref: http://lpaste.net/2450854973576052736 *)
Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [| (t1, t2) t].
  Case "l = []".
    intros l1 l2 eq. inversion eq. reflexivity.
  Case "l = (t1, t2) :: t". intros l1 l2 eq. inversion eq.
  simpl. rewrite IHt. reflexivity.
  destruct (split t) as [x1 x2].
    SCase "split t = (x1 x2)". reflexivity.
Qed.

(** **** Exercise: 2 stars (destruct_eqn_practice) *)

(* ref: https://github.com/jwiegley/software-foundations/blob/master/MoreCoq.v *)
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b. destruct b.
  Case "b = true". destruct (f true) eqn:Hft.
    SCase "f true = true". rewrite Hft. apply Hft.
    SCase "f true = false". destruct (f false) eqn:Hff.
      SSCase "f false = true".  apply Hft.
      SSCase "f false = false". apply Hff.
  Case "b = false". destruct (f false) eqn:Hff.
    SCase "f false = true". destruct (f true) eqn:Hft.
      SSCase "f true = true".  apply Hft.
      SSCase "f true = false". apply Hff.
    SCase "f false = false". rewrite Hff. apply Hff.
Qed.

(** **** Exercise: 2 stars (override_same) *)
Theorem override_same : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 ->
  (override f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f eq. unfold override.
  destruct (beq_nat k1 k2) eqn:H.
  Case "beq_nat k1 k2 = true".
    apply beq_nat_true in H. rewrite <- H. symmetry. apply eq.
  Case "beq_nat k1 k2 = false".
    reflexivity.
Qed.

(** * Review *)

(** * Additional Exercises *)

(** **** Exercise: 3 stars (beq_nat_sym) *)
Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    intros m. destruct m as [| m'].
    SCase "m = 0".    reflexivity.
    SCase "m = S m'". apply zero_nbeq_S.
  Case "n = S n'".
    intros m. destruct m as [| m'].
    SCase "m = 0".    apply S_nbeq_0.
    SCase "m = S m'". simpl. apply IHn'.
Qed.

(** **** Exercise: 3 stars, advanced, optional (beq_nat_sym_informal) *)
(** Give an informal proof of this lemma that corresponds to your
    formal proof above:

   Theorem: For any [nat]s [n] [m], [beq_nat n m = beq_nat m n].

   Proof:
   (* TODO *)
[]
 *)

(** **** Exercise: 3 stars, optional (beq_nat_trans) *)
Theorem beq_nat_trans : forall n m p,
  beq_nat n m = true ->
  beq_nat m p = true ->
  beq_nat n p = true.
Proof.
  intros n m p e1 e2.
  apply beq_nat_true in e1.
  apply beq_nat_true in e2.
  rewrite -> e2 in e1.
  rewrite e1. symmetry. apply beq_nat_refl.
Qed.

(** **** Exercise: 3 stars, advanced (split_combine) *)
(** We have just proven that for all lists of pairs, [combine] is the
    inverse of [split].  How would you formalize the statement that
    [split] is the inverse of [combine]?

    Complete the definition of [split_combine_statement] below with a
    property that states that [split] is the inverse of
    [combine]. Then, prove that the property holds. (Be sure to leave
    your induction hypothesis general by not doing [intros] on more
    things than necessary.  Hint: what property do you need of [l1]
    and [l2] for [split] [combine l1 l2 = (l1,l2)] to be true?)  *)

(* ref: https://github.com/tismith/sf/blob/master/MoreCoq.v *)

Definition split_combine_statement : Prop :=
  forall {X Y: Type} (l1 : list X) (l2 : list Y),
  length l1 = length l2 -> split (combine l1 l2) = (l1, l2).

Theorem split_combine : split_combine_statement.
Proof.
  unfold split_combine_statement.
  induction l1 as [| h1 t1].
  Case "l1 = []".
    intros l2 eq.
    destruct l2 as [| h2 t2].
    SCase "l2 = []".
      reflexivity.
    SCase "l2 = h2 :: t2".
      inversion eq.
  Case "l1 = h1 :: t1".
    intros l2 eq.
    induction l2 as [| h3 t3] eqn:Hl2.
    SCase "l2 = []".
      inversion eq.
    SCase "l2 = h3 :: t3".
      inversion eq. apply IHt1 in H0. simpl. rewrite -> H0. reflexivity.
Qed.

(** **** Exercise: 3 stars (override_permute) *)
Theorem override_permute : forall (X:Type) x1 x2 k1 k2 k3 (f : nat->X),
  beq_nat k2 k1 = false ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  intros X x1 x2 k1 k2 k3 f H. unfold override.
  destruct (beq_nat k1 k3) eqn:H13.
  Case "beq_nat k1 k3 = true".
    apply beq_nat_true in H13. rewrite H13 in H.
    rewrite H. reflexivity.
  Case "beq_nat k1 k3 = false".
    destruct (beq_nat k2 k3) eqn:H23.
    SCase "beq_nat k2 k3 = true". reflexivity.
    SCase "beq_nat k2 k3 = false". reflexivity.
Qed.

(** **** Exercise: 3 stars, advanced (filter_exercise) *)
(** This one is a bit challenging.  Pay attention to the form of your IH. *)

(* ref: https://github.com/tismith/sf/blob/master/MoreCoq.v *)

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  intros X test x l. induction l as [| l1 l2].
  Case "l = []".
    intros lf H. inversion H.
  Case "l = l1 :: l2".
    simpl.
    destruct (test l1) eqn:Hl1.
    SCase "test l1 = true".
      intros lf H.
      inversion H. rewrite <- Hl1. inversion H1. reflexivity.
    SCase "test l1 = false".
      apply IHl2.
Qed.

(** **** Exercise: 4 stars, advanced (forall_exists_challenge) *)
(** Define two recursive [Fixpoints], [forallb] and [existsb].  The
    first checks whether every element in a list satisfies a given
    predicate:
      forallb oddb [1;3;5;7;9] = true

      forallb negb [false;false] = true

      forallb evenb [0;2;4;5] = false

      forallb (beq_nat 5) [] = true
    The second checks whether there exists an element in the list that
    satisfies a given predicate:
      existsb (beq_nat 5) [0;2;3;6] = false

      existsb (andb true) [true;true;false] = true

      existsb oddb [1;0;0;0;0;3] = true

      existsb evenb [] = false
    Next, define a _nonrecursive_ version of [existsb] -- call it
    [existsb'] -- using [forallb] and [negb].

    Prove that [existsb'] and [existsb] have the same behavior.
*)

Fixpoint forallb {X : Type} (fn : X -> bool) (l : list X) : bool :=
  match l with
    | nil => true
    | cons h t => match fn h with
               | false => false
               | true  => forallb fn t
             end
  end.

Example test_forallb1:
  forallb oddb [1;3;5;7;9] = true.
Proof. reflexivity. Qed.
Example test_forallb2:
  forallb negb [false;false] = true.
Proof. reflexivity. Qed.
Example test_forallb3:
  forallb evenb [0;2;4;5] = false.
Proof. reflexivity. Qed.
Example test_forallb4:
  forallb (beq_nat 5) [] = true.
Proof. reflexivity. Qed.

Fixpoint existsb {X : Type} (fn : X -> bool) (l : list X) : bool :=
  match l with
    | nil => false
    | cons h t => match fn h with
                    | true  => true
                    | false => existsb fn t
                  end
  end.

Example test_existsb1:
  existsb (beq_nat 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb2:
  existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb3:
  existsb oddb [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb4:
  existsb evenb [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X : Type} (fn : X -> bool) (l : list X) : bool :=
  negb (forallb (fun x => negb (fn x)) l).

Example test_existsb'1:
  existsb' (beq_nat 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb'2:
  existsb' (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb'3:
  existsb' oddb [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb'4:
  existsb' evenb [] = false.
Proof. reflexivity. Qed.

Theorem ex_existsb' : forall {X : Type} (fn : X -> bool) (l : list X),
  existsb fn l = existsb' fn l.
Proof.
  intros X fn l. induction l as [| h t].
  Case "l = []".
    unfold existsb'. reflexivity.
  Case "l = cons h t".
    simpl. destruct (fn h) eqn:H.
    SCase "fn h = true".
      unfold existsb'. simpl.
      rewrite H. reflexivity.
    SCase "fn h = false".
      unfold existsb'.
      simpl. rewrite H. simpl.
      unfold existsb' in IHt.
      apply IHt.
Qed.