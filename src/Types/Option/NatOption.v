(* An implementation of the 'NatOption' type *)

(* Import {Natlist,Induction} *)
Require Export Nat.
Require Import NatList.
Require Import Induction.

(* //////////// NATOPTION \\\\\\\\\\\\\\ *)
Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

(* Function that returns the number at a position, or None otherwise *)
Fixpoint nth_nat_element (l : natlist) (n : nat) : natoption :=
  match l with
  | [ ] => None
  | h :: t => match (beq_nat n O) with
             | true => h
             | false => (nth_nat_element t (pred n))
             end
  end.

Definition option_elim (d : nat) (n : natoption) : nat :=
  match n with
  | Some n' => n'
  | None => d
  end.

(* Essential to note that → conditional expression ≡ match statements where decision flow is trivial *)

(* hd function with support for option elimination *)
Definition hd_error (l : natlist) : natoption :=
  match l with
  | [ ] => None
  | h :: t => Some h
  end.

Theorem option_elim_hd : forall l : natlist, forall n : nat,
  hd n l = option_elim n (hd_error l).
Proof
  intros l n.
  induction l as [| n1 l1 IHl1].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
