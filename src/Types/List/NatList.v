(* An implementation of the 'NatList' Data-Structure as an Algebraic Type *)

(* Import the Types : {Nat,Bool} + Inductive Proofs *)
Require Export Nat.
Require Import Induction.

(* ////////// NATPAIR \\\\\\\\\\\ *)

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

(* ////////// NATLIST \\\\\\\\\\\ *)

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

(* ////////// BAG \\\\\\\\\\\ *)

(* An implementation of a 'bag' ('multiset') as a 'natlist' *)
Definition bag := natlist.

(* Counts the number of elements in a bag that are equal to some value *)
Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | [ ] => O
  | h :: t => match (beq_nat h v) with
              | true => (plus (S O) (count v t))
              | false => (count v t)
              end
  end.

(* Sum basically _Unions_ two bags [without removing duplicates] *)
Definition sum (b1 b2 : bag) : bag :=
  (app b1 b2).

(* Add basically adds an element to the bag *)
Definition add (v : nat) (s : bag) : bag :=
  (app [v] s).

(* Member checks whether a given element belongs to the bag *)
Definition member (v : nat) (s : bag) : bool :=
  match (count v s) with
  | O => false
  | _ => true
  end.

(* A helper function for 'remove_one' *)
Fixpoint remove_one_helper (v : nat) (s : bag) (safe : bag) : bag :=
  match s with
  | [ ] => safe
  | h :: t => match (beq_nat v h) with
              | true => (safe ++ t)
              | false => (remove_one_helper v t (safe ++ [h]))
              end
  end.

(* Removes an [first] instance of 'v' from 's' *)
Fixpoint remove_one (v : nat) (s : bag) : bag :=
  (remove_one_helper v s [ ]).

(* A helper function for 'remove_all' *)
Fixpoint remove_all_helper (n : nat) (v : nat) (s : bag) : bag :=
  match n with
  | O => s
  | S n' => (remove_all_helper n' v (remove_one v s))
  end.

(* Removes [all] occurences of 'v' in 's' from 's' *)
Fixpoint remove_all (v : nat) (s : bag) : bag :=
  (remove_all_helper (count v s) v s).

(* Checks whether bag b1 is a subset of bag b2 *)
Fixpoint subset (s1 : bag) (s2 : bag) : bool :=
  match s1 with
  | [ ] => true
  | h :: t => match (leq_nat (count h s1) (count h s2)) with
              | true => (subset t s2)
              | false => false
              end
  end.

(* Reversing a List *)
Fixpoint rev (l : natlist) : natlist :=
  match l with
  | [ ] => [ ]
  | h :: l' => (rev l') ++ [h]
  end.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1 with
  | [ ] => match l2 with
           | [ ] => true
           | h :: t => false
           end
  | h1 :: t1 => match l2 with
                | [ ] => false
                | h2 :: t2 => match (beq_nat h1 h2) with
                              | true => (beq_natlist t1 t2)
                              | false => false
                              end
                end
  end.

(* ////////// PROOFS \\\\\\\\\\\ *)

(* Exercises on {NatList,Bag,NatPair} with Induction *)

(* Theorem relating the functions : {count,add} *)
Theorem count_add_element : forall (v : nat) (s : bag),
  (count v (add v s)) = (count v s) + (S O).
Proof.
Admitted.

(* Some simple facts about {NatList} *)
Theorem nil_app : forall l : natlist,
  [ ] ++ l = l.
Proof.
  intros l.
  simpl.
  reflexivity.
Qed.

Theorem tl_length_pred : forall l : natlist,
    pred (length l) = length (tl l).
Proof.
  intros l.
  destruct l as [| n l'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* To prove that the length of a list is equal to its reverse, we need to show that :
   length (l1 ++ l2) = length l1 + length l2 *)
Theorem app_assoc : forall l1 l2 l3 : natlist,
  l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
  intros l1 l2 l3.
  induction l1 as [| n l1' IHl1'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem length_concat : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2.
  induction l1 as [| n' l1' IHl1'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHl1'. simpl. reflexivity.
Qed.

Theorem length_rev : forall l : natlist,
  length l = length (rev l).
Proof.
  intros l.
  induction l as [| n' l1' IHl1'].
  - simpl. reflexivity.
  - simpl. rewrite -> length_concat. simpl. rewrite -> IHl1'. rewrite -> plus_comm. reflexivity.
Qed.

Theorem app_nil_r : forall l : natlist,
  l ++ [ ] = l.
Proof.
  intros l.
  induction l as [| n' l1' IHl1'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem rev_app_distr : forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2.
  induction l1 as [| n' l1' IHl1'].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl1'. rewrite <- app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l.
  induction l as [| n' l1' IHl1'].
  - simpl. reflexivity.
  - simpl. rewrite -> rev_app_distr. rewrite -> IHl1'. simpl. reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  induction l1 as [| n' l1' IHl1'].
  - simpl. rewrite -> app_assoc. reflexivity.
  - simpl. simpl. simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem distribute_elem_concatenation : forall l1 l2 : natlist, forall n : nat,
  n :: (l1 ++ l2) = (n :: l1) ++ l2.
Proof.
  intros n l1 l2.
  induction l1 as [| n' l1' IHl1'].
  - simpl. reflexivity.
  - simpl. simpl. reflexivity.
Qed.
      
Theorem nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1 as [| n' l1' IHl1'].
  - simpl. reflexivity.
  - induction n' as [| n'' IHn''].
      simpl. rewrite -> IHl1'. reflexivity.
      simpl. rewrite -> IHl1'. rewrite -> distribute_elem_concatenation. reflexivity.
 Qed.

Theorem beq_natlist_refl : forall l : natlist,
  true = beq_natlist l l.
Proof.
  intros l.
  induction l as [| n l' IHl'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHl'. rewrite <- beq_nat_refl. reflexivity.
Qed.
  
Theorem count_member_nonzero : forall s : bag,
  leq_nat (S O) (count (S O) ((S O) :: s)) = true.
Proof.
  intros s.
  induction s as [| n' l' IHl'].
  - simpl. reflexivity.
  - induction n' as [| n'' IHn''].
    simpl. rewrite <- IHl'. simpl. reflexivity.
    simpl. reflexivity.
Qed.

Theorem leq_nat_n_Sn : forall n,
  leq_nat n (S n) = true.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.
  