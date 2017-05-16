(* An implementation of the 'NatList' Data-Structure as an Algebraic Type *)

(* Import the Types : {Nat,Bool} + Inductive Proofs *)
Require Export Nat.
Require Import Induction.

(* 1) Implement a Type : NatPair -> Pair of Natural Numbers *)
Inductive natpair : Type :=
  | pair : nat -> nat -> natpair.

(* Convenient notation for a 'pair' *)
Notation "( x , y )" := (pair x y).

(* Functions to extract the {first, second} elements of a natpair *)
Definition fst (p: natpair) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd(p: natpair) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p: natpair) : natpair :=
  match p with
  | (x,y) => (y,x)
  end.

(* Proof of Surjectivity *)
Theorem surjective_pairs_sugar : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  intros n m.
  reflexivity.
Qed.

Theorem surjective_pairs : forall (p : natpair),
  p = (fst p, snd p).
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

(* Proofs of 'swap' properties *)
Theorem snd_fst_is_swap : forall (p : natpair),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natpair),
  fst (swap_pair p) = snd p.
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

(* We can now implementation the {natlist} Datatype *)
Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

(* Convenient notations for a 'NatList' *)
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* {Repeat, Length, Append} functions *)
Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
  | [ ] => O
  | h :: t => S (length t)
  end.

Fixpoint app (lone ltwo : natlist) : natlist :=
  match lone with
  | [ ] => ltwo
  | h :: t => h :: (app t ltwo)
  end.

(* Notation for the append function *)
Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

(* Implementations of the {hd,tl} functions *)
Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | [ ] => default
  | h :: t => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | [ ] => [ ]
  | h :: t => t
  end.

(* Some Recursive Functions over NatList *)
Fixpoint nonzeros (l : natlist) : natlist :=
  match l with
  | [ ] => [ ]
  | h :: t => match h with
              | O => nonzeros t
              | S n => h :: (nonzeros t)
              end
  end.

Fixpoint oddmembers (l : natlist) : natlist :=
  match l with
  | [ ] => [ ]
  | h :: t => match (odd_nat h) with
              | true => h :: (oddmembers t)
              | false => (oddmembers t)
              end
  end.

Definition countoddmembers (l : natlist) : nat :=
  (length (oddmembers l)).

(* The 'zipping' function to interweave 2 natlists *)
Fixpoint alternate (lone ltwo : natlist) : natlist :=
  match lone with
  | [ ] => ltwo
  | h :: t => match ltwo with
              | [ ] => lone
              | h' :: t' => h :: h' :: (alternate t t')
              end
  end.

Example test_alternate1:
  alternate [(S O);(S (S O));(S (S (S O)))] [O;(S (S (S (S O))));(S O)] = [S O; O; S (S O); S (S (S (S O))); S (S (S O)); S O].
Proof. simpl. reflexivity. Qed.

Example test_alternate2:
  alternate [O] [(S O);(S (S O));(S (S (S O)))] = [O;(S O);(S (S O));(S (S (S O)))].
Proof. simpl. reflexivity. Qed.

Example test_alternate3:
  alternate [O;(S O);(S (S O))] [(S (S (S O)))] = [O;(S (S (S O)));(S O);(S (S O))].
Proof. simpl. reflexivity. Qed.
