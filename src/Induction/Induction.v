Require Export Nat.

(* We will use the 'nat','bool' types here. *)

(* Let's begin with an Example Theorem that we prove by Induction *)
Theorem plus_n_O: forall n: nat,
n = n + O.
Proof.
intros n.
induction n as [|n' IHn'].
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
Theorem mult_O_r: forall n: nat,
n * O = O.
Proof.
intros n. induction n as [|n' IHn'].
- simpl. reflexivity.
- simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm: forall n m: nat,
S (n + m) = n + (S m).
Proof.
intros n m. induction n as [| n' IHn'].
- simpl. reflexivity.
- simpl. rewrite -> IHn'. simpl. reflexivity.
Qed.

Theorem plus_comm: forall n m: nat,
n + m = m + n.
Proof.
intros n m. induction n as [| n' IHn'].
- simpl. rewrite <- plus_n_O. reflexivity.
- simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc: forall n m o: nat,
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
