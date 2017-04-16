Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negate_bool (b:bool) : bool :=
  match b with
  | true => false
  | false => true
end.

Definition and_bool (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
end.

Definition or_bool (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
end.

Definition xor_bool (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => (negate_bool b2)
  | false => b2
end.

Definition nand_bool (b1:bool) (b2:bool) : bool :=
  negate_bool (and_bool b1 b2).

Example test_nand_bool1: (nand_bool true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nand_bool2: (nand_bool true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_nand_bool3: (nand_bool false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nand_bool4: (nand_bool false false) = true.
Proof. simpl. reflexivity. Qed.

Infix "&&" := and_bool.
Infix "||" := or_bool.

(* The infix notation is handy to chain and evaluate multiple arguments *)
Example test_or_bool1: false || true || true = true.
Proof. simpl. reflexivity. Qed.

(* The command : Admitted acts as a placeholder for a 'Proof' that isn't formally proved *)

Definition and_bool_3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true => (and_bool b2 b3)
  | false => false
end.

Example test_and_bool_31: (and_bool_3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_and_bool_32: (and_bool_3 true true false) = false.
Proof. simpl. reflexivity. Qed.
Example test_and_bool_33: (and_bool_3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_and_bool_34: (and_bool_3 true false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_and_bool_35: (and_bool_3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_and_bool_36: (and_bool_3 false true false) = false.
Proof. simpl. reflexivity. Qed.
Example test_and_bool_37: (and_bool_3 false false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_and_bool_38: (and_bool_3 false false false) = false.
Proof. simpl. reflexivity. Qed.

(* One can use the  : 'Check' command to verify the Types of computations *)
Check true.
(* ===> true: bool *)
Check negate_bool.
(* ===> negate_bool : bool -> bool *)



(* Proving that if an 'and' expression is true, then so is the second argument. *)
(* We'll use destruction on b *)
(* We also need to prove the commutativity of 'and_bool' first *)
Theorem andb_commutative: forall b c : bool,
  and_bool b c = and_bool c b.
Proof.
  intros b c.
  destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.


Theorem and_is_second_arg: forall b c: bool,
c = true -> and_bool c b = b.
Proof.
intros b c.
intros H.
rewrite -> H.
reflexivity.
Qed.

(* Exercise 2 : Prove that if and x y = or x y, then x = y *)
(* First let's prove somthing simpler -> The other direction *)
Theorem eq_andb_orb : forall b c: bool,
b = c -> (and_bool b c = or_bool b c).
Proof.
intros b c.
intros H.
rewrite -> H.
destruct c.
- reflexivity.
- reflexivity.
Qed.

(* Main Theorem *)
Theorem andb_eq_orb : forall b c: bool,
(and_bool b c = or_bool b c) -> b = c.
Proof.
intros b c.
destruct b.
- simpl. intros H. rewrite -> H. reflexivity.
- simpl. intros H. rewrite -> H. reflexivity.
Qed.
