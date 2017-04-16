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
Definition leq_nat (n m : nat) : bool :=
  match n with 
  | O => true
  | S n' => match (minus_2 n m) with
            | O => true
            | S num => false
            end
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
Theorem plus_id_transitive: forall n m o: nat,
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
Theorem mult_S_n_1 : forall n m : nat,
  m = S n -> m * ((S O) + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> plus_1_n_l.
  rewrite -> H.
  reflexivity. Qed.

(* When the _evaluation_ of an argument itself is recursive, then
proofs can't simply use _rewrite_ or _simpl_ -> Use _destruct_ *)
Theorem plus_1_neq_O : forall n : nat,
  beq_nat (n + (S O)) O = false.
Proof.
  intros n. destruct n as [|n'].
  - reflexivity.
  - reflexivity. Qed.

(* Proof that 1 plus anything can never be zero in the realm of the natural numbers *)
Theorem zero_nbeq_plus_1: forall n: nat,
beq_nat O (n + (S O)) = false.
Proof.
intros n. destruct n as [|n'].
- reflexivity.
- reflexivity. Qed.

(* Exercise 1 : Show that the identity function applied twice is the same as it being applied once *)
(* //TODO : Juspreet *)
Theorem identity_fn_applied_twice : forall (f : bool -> bool),
(forall (x: bool), f x = x) -> forall (b: bool), f (f b) = b.
Proof.
Admitted.

(* Exercise 3 : We will buld a representation of Natural Numbers using 0, Odd-ness, Even-ness *)
Inductive natBinary : Type :=
  | I : natBinary
  | Ev : natBinary -> natBinary
  | Od : natBinary -> natBinary.

Fixpoint incr (n: natBinary) : natBinary :=
  match n with
    | I => Od I 
    | Ev n' => Od n'
    | Od n' => Ev (incr n')
end.

Fixpoint bin_to_nat (bin: natBinary) : nat :=
  match bin with
    | I => O
    | Ev bin' => plus (bin_to_nat bin') (bin_to_nat bin')
    | Od bin' => plus (S O) (plus (bin_to_nat bin') (bin_to_nat bin'))
end.

Example test_bin_incr1 : (incr (Od (Od (Od I)))) = (Ev (Ev (Ev (Od I)))).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr2 : (incr (Ev (Od (Od I)))) = (Od (Od (Od I))).
Proof. simpl. reflexivity. Qed.
Example test_bin_to_nat1 : (bin_to_nat (Ev (Od (Od I)))) = (S (S (S (S (S (S O)))))).
Proof. simpl. reflexivity. Qed.
Example test_bin_to_nat2 : (bin_to_nat (Od (Ev (Od I)))) = (S (S (S (S (S O))))).
Proof. simpl. reflexivity. Qed.
Example test_incr_and_bin_to_nat1 : (plus (bin_to_nat (Od (Ev (Od I)))) (S O)) = (bin_to_nat (incr (Od (Ev (Od I))))).
Proof. simpl. reflexivity. Qed.


