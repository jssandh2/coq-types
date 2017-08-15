Require Export NatList.
Require Export Nat.
Require Import Induction.

(* /////////////////// POLYMOPHIC LISTS \\\\\\\\\\\\\\\\\\\\\\ *)
(* Let's introduce generic types, and the 'Type' → Type ≡ * , ∋ , ∀ t , t : * ≡ Type *)
Inductive list (X : Type) : Type :=
  | nil : list X                  (* nil : ∀ X : Type, list X *)
  | cons : X -> list X -> list X.   (* cons : ∀ X : Type, X → list X → list X *)

(* Implementation of Polymorphic functions for Lists *)
Fixpoint repeat' (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | O => nil X
  | S count' => cons X x (repeat' X x count')
  end.

(* We can _substantially_ simplify snytax by leaving out input type annotations, as Coq will use Type Inference *)
(* Type Inference - repeat'' *)
Fixpoint repeat'' X x count : list X :=
  match count with
  | O => nil X
  | S count' => cons X x (repeat'' X x count')
  end.

(* For both cases, Coq will Type Inference `repeat''` as :
  ∀ X : Type, X → nat → list X *)

(* We can avoid '_' by asserting the implicit arguments that Coq must always determine by Type Inference *)
(* Imnplicitness must be associated in one-to-one correspondence with some Function *)
Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat' {X} x count.

(* We can also make function arguments implicit by surrounding them with : {} *)
Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | O => nil
  | S count' => cons x (repeat''' x count')
  end.

(* We can extend the idea of implicitness to writing Inductive Types *)
Inductive list' {X : Type} : Type :=
  | nil' : list'
  | cons' : X -> list' -> list'.
(* NOTE : THE ABOVE IS NOT USED, BECAUSE, list' nat ≡ list' bool IN type-signature *)

(* Implicit + Polymorphic re-implementation of standard List Functions *)
Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => O
  | cons h t => S (length t)
  end.

(* Some convenient notation again *)
(* The implicitness allows the constructors to be written as before *)
Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(* ////////// PROOFS 1 \\\\\\\\\\\\\ *)
Theorem app_nil_r : forall X : Type, forall l : list X,
  l ++ [ ]  = l.
Proof.
  intros X l.
  induction l as [| n1 l1 IHl1].
  - simpl. reflexivity.
  - simpl. rewrite -> IHl1. reflexivity.
Qed.

Theorem app_assoc : forall A : Type, forall l1 l2 l3 : list A,
  l1 ++ l2 ++ l3 = (l1 ++ l2) ++ l3.
Proof.
  intros A l1 l2 l3.
  induction l1 as [| n1 l1' IHl1'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHl1'. reflexivity.
Qed.

Theorem app_length : forall X : Type, forall l1 l2 : list X,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros X l1 l2.
  induction l1 as [| n' l1' IHl1'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHl1'. simpl. reflexivity.
Qed.

Theorem rev_app_distr : forall X : Type, forall l1 l2 : list X,
  rev (app l1 l2) = app (rev l2) (rev l1).
Proof.
  intros X l1 l2.
  induction l1 as [| n l1' IHl1'].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl1'. rewrite <- app_assoc. reflexivity.
Qed.
  
Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l.
  induction l as [| n l' IHl'].
  - simpl. reflexivity.
  - simpl. rewrite -> rev_app_distr. rewrite -> IHl'. simpl. reflexivity.
Qed.

(* //////////// POLYMORPHIC PAIRS \\\\\\\\\\\\\\\\\\\ *)
Inductive prod (X Y : Type) : Type :=
| pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.
(* "type_scope" : Tells Coq to only use (X * Y) when parsing types, thereby, avoiding a clash with the multliplication symbol *)

(* Projection Functions *)
Definition fst {X Y : Type} (p : X * Y) :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) :=
  match p with
  | (x, y) => y
  end.

(* Zip ≡ Combine *)
Fixpoint combine {X Y : Type} (l1 : list X) (l2 : list Y): list (X * Y) :=
  match l1, l2 with
  | nil, _ => [ ]
  | _, nil => [ ]
  | x1 :: t1, x2 :: t2 => (x1, x2) :: (combine t1 t2)
  end.

(* Split ≡ ¬ Combine *)
Fixpoint split {X Y : Type} (l : list (X * Y)) : ((list X) * (list Y)) :=
  match l with
  | [ ] => ([ ], [ ])
  | (x1, y1) :: t => pair (x1 :: (fst (split t))) (y1 :: (snd (split t))) 
  end.

(* //////////// POLYMORPHIC OPTIONS \\\\\\\\\\\\\\\ *)
Inductive option (X : Type): Type :=
| Some : X -> option X
| None : option X.

Arguments Some {X} _.
Arguments None {X}.

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
  match l with
  | [ ] => None
  | h :: t => match n with
             | O => Some h
             | _ => nth_error t (pred n)
             end          
  end.

Definition hd_error {X : Type} (l : list X): option X :=
  match l with
  | [ ] => None
  | h :: t => Some h
  end.

(* /////////////// HIGHER-ORDER FUNCTIONS + ANONYMOUS FUNCTIONS \\\\\\\\\\\\\\\\\\\\ *)

(* Coq allows Functions to be passed around → Higher-Order Functions *)
(* {Map,Filter,Fold} *)

Fixpoint filter {X : Type} (f : X -> bool) (l : list X) : list X :=
  match l with
  | [ ] => [ ]
  | h :: t => match f h with
             | true => h :: (filter f t)
             | false => filter f t
             end
  end.

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | [ ] => [ ]
  | h :: t => (f h) :: (map f t)
  end.

Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (acc : Y) : Y :=
  match l with
  | [ ] => acc
  | h :: t => f h (fold f t acc)
  end.

(* The "fun" keyword allows for the definition of anonymous functions. 'fun' ≡ λ *)

(* A Helper Bool Function *)
Definition and_bool (b1 b2 : bool) : bool :=
  match b1, b2 with
  | true, true => true
  | _, _ => false
  end.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => (and_bool (even_nat n) (negate_bool (leq_nat n (S (S (S (S (S (S O)))))))))) l.

Definition failure_test {X : Type} (x : X) (y : list X * list X) (z : X -> bool) : list X * list X :=
  match z x with
  | true => pair (x :: (fst y)) (snd y)
  | false => pair (fst y) (x :: (snd y))
  end.

Definition partition {X : Type} (test : X -> bool) (l : list X) : list X * list X :=
  fold (fun x y => (failure_test x y test)) l (pair [ ] [ ]).

(* /////////////// PROOFS \\\\\\\\\\\\\\\\\\\ *)
 
Theorem map_rev : forall X Y : Type, forall f : X -> Y, forall l : list X,
  map f (rev l) = rev (map f l).
(* Proof.
  intros X Y f l.
  induction l as [| n l' IHl'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHl'. reflexivity.
Qed. *)
Admitted.

Compute (partition (fun n => leq_nat n (S (S (S O)))) [O;(S O);(S (S (S (S O))));(S (S (S (S (S O)))));(S (S O))]).