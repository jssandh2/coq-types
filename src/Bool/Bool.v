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
  (negate_bool (and_bool b1 b2))
end.

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

Definition nand_bool_3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true => (nand_bool b2 b3)
  | false => false
end.

Example test_nand_bool_31: (nand_bool_3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nand_bool_32: (nand_bool_3 true true false) = false.
Proof. simpl. reflexivity. Qed.
Example test_nand_bool_33: (nand_bool_3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_nand_bool_34: (nand_bool_3 true false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_nand_bool_35: (nand_bool_3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_nand_bool_36: (nand_bool_3 false true false) = false.
Proof. simpl. reflexivity. Qed.
Example test_nand_bool_37: (nand_bool_3 false false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_nand_bool_38: (nand_bool_3 false false false) = false.
Proof. simpl. reflexivity. Qed.

(* One can use the  : 'Check' command to verify the Types of computations *)
Check true.
(* ===> true: bool *)
Check negate_bool.
(* ===> negate_bool : bool -> bool *)



