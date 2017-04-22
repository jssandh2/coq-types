Require Export Nat.

(* We will use the 'nat','bool' types here. *)

(* Let's begin with an Example Theorem that we prove by Induction *)
Theorem plus_n_O : forall n: nat,
n = n + O.
Proof.
intros n. induction n as [|n' IHn'].
- (* n = O *) reflexivity.
- (* n = S n' *) simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem minus_diag : forall n,
minus n n = O.
Proof.
intros n. induction n as [|n' IHn'].
- simpl. reflexivity.
- simpl. rewrite <- IHn'. reflexivity.
Qed.

(* Exercise 1 : Basic Induction Exercises *)
Theorem mult_O_r : forall n: nat,
n * O = O.
Proof.
intros n. induction n as [|n' IHn'].
- simpl. reflexivity.
- simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m: nat,
S (n + m) = n + (S m).
Proof.
intros n m. induction n as [| n' IHn'].
- simpl. reflexivity.
- simpl. rewrite -> IHn'. simpl. reflexivity.
Qed.

Theorem plus_comm : forall n m: nat,
n + m = m + n.
Proof.
intros n m. induction n as [| n' IHn'].
- simpl. rewrite <- plus_n_O. reflexivity.
- simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m o: nat,
n + (m + o) = (n + m) + o.
Proof.
intros n m o. induction n as [| n' IHn'].
- simpl. reflexivity.
- simpl. rewrite -> IHn'. simpl. reflexivity.
Qed.

(* Exercise 2 : Induction on 'double_plus' *)

(* The double function *)
Fixpoint double (n: nat) : nat :=
  match n with
    | O => O
    | S n' => S (S (double n'))
end.

Lemma double_plus : forall n: nat,
double n = n + n.
Proof.
intros n. induction n as [|n' IHn'].
- simpl. reflexivity.
- simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. rewrite -> plus_comm. rewrite -> plus_n_Sm. reflexivity.
Qed.

(* NOTE : 'destruct' enumerates *finite* possible values for a type *)
(* NOTE : 'induction' sets up a proposition by having a base case proved, assuming the IH, and then proving a general statement *)

(* Introductin of the 'assert' tactic : Refer to _local_ theorems in lexical-scope. *)
Theorem mult_O_plus : forall n m: nat,
(O + n) * m = n * m.
Proof.
intros n m.
assert (H: O + n = n). { reflexivity. }
rewrite -> H.
reflexivity.
Qed.

(* Another use case of the 'assert' tactic is to allow flexible 'rewrite' by introducing hypotheses in a smarter way *)
Theorem plus_rearrange : forall n m p q: nat,
(n + m) + (p + q) = (m + n) + (p + q).
Proof.
intros n m p q.
assert (H: n + m = m + n). { rewrite -> plus_comm. reflexivity. }
rewrite -> H.
reflexivity.
Qed.

(* Informal Proof : Commutativity of addition *)
(* Goal : n + m = m + n *)
(* Proof. *)
(* intros n. induction n as [| n' IHn'] *)
(* For n = O -> O + n = n + O -> {rewrite <- plus_n_O} -> O + n = n -> {simpl.} -> n = n -> {reflexivity.} *)
(* For n = S n' -> S n' + m = m + S n' -> S(n' + m) = m + S n' -> {rewrite -> IHn'.} -> S(m + n') = m + S n' -> {rewrite -> plus_n_Sm} -> m + S n' = m + S n'-> {reflexivity.} *)
(* Qed. *)

(* Exercise 2 : More Exercises *)
(* Main Theorem 1 *) 
Theorem plus_swap : forall n m p: nat,
n + (m + p) = m + (n + p).
Proof.
intros n m p.
assert (H1: n + (m + p) = (n + m) + p). { rewrite -> plus_assoc. reflexivity. }
assert (H2: m + (n + p) = (m + n) + p). { rewrite -> plus_assoc. reflexivity. }
rewrite -> H1.
rewrite -> H2.
assert (H3: n + m = m + n). { rewrite -> plus_comm. reflexivity. }
rewrite -> H3.
reflexivity.
Qed.

Theorem add_term_mult_succ : forall n m: nat,
m + (m * n) = m * (S n).
Proof.
intros n m. induction m as [|m' IHm'].
- simpl. reflexivity.
- simpl. rewrite <- IHm'. rewrite -> plus_swap. reflexivity.
Qed.

(* Main Theorem 2 *) 
Theorem mult_comm : forall n m: nat,
n * m = m * n.
Proof.
intros n m. induction n as [|n' IHn'].
- simpl. rewrite -> mult_O_r. simpl. reflexivity.
- simpl. rewrite -> IHn'. rewrite -> add_term_mult_succ. reflexivity.
Qed.