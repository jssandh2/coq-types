(* nat --> An 'Inductive' Type, and not an 'enumerated' type [Ex: Bool] *)
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n:nat) : nat :=
  match n with
    | O => O
    | S n' => n'
end.

(* Quick redefinition of : bool *)
Inductive bool : Type :=
  | true : bool
  | false : bool.

(* Verify the Number 3 *)
Check (S (S (S O))).

(* Using recusrion with : Fixpoint *)
Fixpoint odd_nat (n:nat) : bool :=
  match n with
  | O => false
  | S O => true 
  | S (S n') => odd_nat n'
end.

Fixpoint even_nat (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even_nat n'
end.

Compute (even_nat (S (S (S (S O))))).
Check even_nat.
Check pred.
Check S.

(* A few Tests [Asserted as Proofs] *)
Example test_even_nat1 : even_nat (S (S (S (S O)))) = true.
Proof. simpl. reflexivity. Qed.
Example test_odd_nat1 : (odd_nat (S (S (S (S O))))) = false.
Proof. simpl. reflexivity. Qed.

(* Definition of the plus, minus, mult and fac functions *)
Fixpoint plus (n:nat) (m:nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
end.

Compute (plus (S (S (S O))) (S (S O))).

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O, _ => O
  | S _, O => n
  | S n', S m' => minus n' m'
end.

Fixpoint minus_2 (n:nat) (m:nat) : nat :=
  match m with
  | O => n
  | S m' => minus_2 (pred n) m'
end.

Compute (minus_2 (S (S (S (S (S O))))) (S (S O))).

Fixpoint mult (n:nat) (m:nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
end.

Fixpoint fac (n:nat) : nat :=
  match n with
  | O => S O
  | S O => S O
  | S n' => mult n (fac n')
end.

(* Simple Tests [Asserted as Proofs] for mult, etc. *)
Example test_fac_1: (fac (S (S (S O)))) = (S (S (S (S (S (S O)))))).
Proof. simpl. reflexivity. Qed.
Example test_mult_1: (mult (S (S O)) (S (S (S O)))) = (S (S (S( S( S( S O)))))).
Proof. simpl. reflexivity. Qed.
Example test_minus_1: (minus (S (S (S (S (S O))))) (S (S (S O)))) = (S (S O)).
Proof. simpl. reflexivity. Qed.
Example test_minus_2: (minus_2 (S (S (S (S (S O))))) (S (S (S O)))) = S (S O).
Proof. simpl. reflexivity. Qed.

(* Introduce notations *)
Notation "x + y" := (plus x y)
                        (at level 50, left associativity)
                        : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

(* Define Equality between 'nat' *)
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

Example test_beq_nat_1: (beq_nat (S (S (S O))) (S (S (S O)))) = true.
Proof. simpl. reflexivity. Qed.
Example test_beq_nat_2: (beq_nat (S (S (S O))) (S (S O))) = false.
Proof. simpl. reflexivity. Qed.

(* Define a function to test : n <= m, without using 'Fixpoint' *)
Fixpoint leq_nat (n m : nat) : bool :=
  match n, m with
  | O, _ => true
  | S _, O => false
  | S n', S m' => leq_nat n' m'
end.

(* Some computations of 'leq' before the Proofs *)
Compute (leq_nat (S (S (S O))) (S (S (S O)))).
Compute (leq_nat (S (S (S O))) (S (S (S (S O))))).
Compute (leq_nat (S (S (S (S O)))) (S (S (S O)))).

Example test_leq_nat1: (leq_nat (S (S (S O))) (S (S (S O)))) = true.
Proof. simpl. reflexivity. Qed.
Example test_leq_nat2: (leq_nat (S (S (S O))) (S (S (S (S O))))) = true.
Proof. simpl. reflexivity. Qed.
Example test_leq_nat3: (leq_nat (S (S (S (S O)))) (S (S (S O)))) = false.
Proof. simpl. reflexivity. Qed.

(* Let us write a few Theorems regarding the type : nat *)

(* Left addition of 0 *)
Theorem plus_O_n_l : forall n: nat, O + n = n.
Proof.
  intros n. reflexivity. Qed. (* simpl is not needed *)

(* To Coq, Lemma = Fact = Remark = Example = Theorem *)
(* The difference is mostly Syntactic Sugar *)

(* Left addition of 1 *)
Theorem plus_1_n_l : forall n: nat, (S O) + n = S n.
Proof.
  intros n. reflexivity. Qed.

(* Using rewrite *)

(* Addition of equal nat *)
Theorem plus_id : forall n m: nat,
n = m ->
n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity. Qed.

(* Addition of transitively equal nat *)
Theorem plus_id_transitive : forall n m o: nat,
n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity. Qed.

(* We can also use rewrite using a _previously_ proved Theorem *)
Theorem add_0_and_mult : forall n m: nat,
(O + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n_l.
  reflexivity. Qed.

(* Proof for Right multiplication by Successor *)
Theorem mult_S_n_1 : forall n m: nat,
m = S n -> m * ((S O) + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> plus_1_n_l.
  rewrite -> H.
  reflexivity. Qed.

(* When the _evaluation_ of an argument itself is recursive, then
proofs can't simply use _rewrite_ or _simpl_ -> Use _destruct_ *)
Theorem plus_1_neq_O : forall n: nat,
beq_nat (n + (S O)) O = false.
Proof.
  intros n. destruct n as [|n'].
  - reflexivity.
  - reflexivity. Qed.

(* Proof that 1 plus anything can never be zero in the realm of the natural numbers *)
Theorem zero_nbeq_plus_1 : forall n: nat,
beq_nat O (n + (S O)) = false.
Proof.
intros n. destruct n as [|n'].
- reflexivity.
- reflexivity. Qed.

(* Exercise 1 : Show that the identity function applied twice is the same as it being applied once *)
Theorem identity_fn_applied_twice : forall (f : bool -> bool),
(forall (x: bool), f x = x) -> (forall (b: bool), f (f b) = b).
Proof.
intros f H b.
rewrite <- H.
simpl.
rewrite <- H.
reflexivity.
Qed.

Theorem unnecess_brack_add : forall n m p: nat,
p + (n + m) = p + n + m.
Proof.
intros n m p. induction p as [|p' IHp'].
- simpl. reflexivity.
- simpl. rewrite -> IHp'. simpl. reflexivity.
Qed.

(* A List of Proofs about Functions of `Nat` from Chapter-3 (Induction) *)
(* NOTE : Not all _require_ Induction. In fact, the goal is to skillfully be minimal in the proofs *)
Theorem leq_nat_refl : forall n: nat,
true = leq_nat n n.
Proof.
intros n. induction n as [|n' IHn'].
- simpl. reflexivity.
- simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem zero_nbeq_S : forall n: nat,
beq_nat O (S n) = false.
Proof.
intros n.
simpl.
reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p: nat,
leq_nat n m = true -> leq_nat (p + n) (p + m) = true.
Proof.
intros n m p H. induction p as [|p' IHp'].
- simpl. rewrite -> H. reflexivity.
- simpl. rewrite -> IHp'. reflexivity.
Qed.

Theorem S_nbeq_O : forall n: nat,
  beq_nat (S n) O = false.
Proof.
intros n.
simpl.
reflexivity.
Qed.

(* Temporary re-proof {already done in Induction.v} of plus_n_O *)
Theorem plus_n_O : forall n: nat,
n = n + O.
Proof.
intros n. induction n as [|n' IHn'].
- (* n = O *) reflexivity.
- (* n = S n' *) simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem mult_1_l : forall n: nat, 
(S O) * n = n.
Proof.
intros n. induction n as [|n' IHn'].
- simpl. reflexivity.
- simpl. rewrite <- plus_n_O. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p: nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
intros n m p. induction n as [|n' IHn'].
- simpl. reflexivity.
- simpl. rewrite -> IHn'. rewrite -> unnecess_brack_add. reflexivity.
Qed.

Theorem beq_nat_refl : forall n: nat,
true = beq_nat n n.
Proof.
intros n. induction n as [|n' IHn'].
- simpl. reflexivity.
- simpl. rewrite -> IHn'. simpl. reflexivity.
Qed.


