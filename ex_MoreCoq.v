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
