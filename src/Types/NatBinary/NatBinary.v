Require Export Nat.

(* NOTE : This file builds the Type : natBinary, which can be thought of as
  built up using {Even, Odd, Identity} Lambda Terms, as opposed to the
  {S,O} definitons introduced for Type Nat *)

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

(* Some Unit Tests *)
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


(* Before we begin proving too much, let's just prove some subsidiary Theorems,
copied from Induction.v in src/Induction/ *)
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

(* This Theorem asserts that : *)
(* incr AND bin_to_nat are commutative operators *)
Theorem bin_to_nat_pres_inc : forall n: natBinary,
S (bin_to_nat n) = bin_to_nat (incr n).
Proof.
intros n. induction n as [|n' IHn'|n'' IHn''].
- simpl. reflexivity.
- simpl. reflexivity.
- simpl. rewrite <- IHn''. rewrite <- plus_n_Sm. simpl. reflexivity.
Qed.
