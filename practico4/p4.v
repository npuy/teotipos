(* Nicolas Pereira - 5.139.786-4 *)

Section Ejercicio1.

Inductive list (A:Set): Set :=
    listNil : list A |
    listCons : A -> list A -> list A.

Inductive bintree (A:Set): Set :=
    bintreeNil : bintree A |
    bintreeCons : A -> bintree A -> bintree A -> bintree A.

Inductive Array (A:Set): nat -> Set :=
    empty : Array A 0 |
    add : forall n:nat, A -> Array A n -> Array A (S n).

Inductive Matrix (A:Set): nat -> nat -> Set :=
    one_col : forall n:nat, Array A n -> Matrix A (S 0) n |
    add_col : forall n m : nat, Matrix A m n -> Array A n -> Matrix A (S m) n.

Inductive leq : nat -> nat -> Prop :=
    leq0 : forall n:nat, leq 0 n |
    leqS : forall n m : nat, leq n m -> leq (S n) (S m).

Inductive eq_list (A:Set) (eqA: A -> A -> Prop): list A -> list A -> Prop :=
    eq_list0 : eq_list A eqA (listNil A) (listNil A) |
    eq_listS : forall (a b:A) (x y:list A), eqA a b -> eq_list A eqA x y -> eq_list A eqA (listCons A a x) (listCons A b y).

Inductive sorted (A:Set) (R:A->A->Prop): list A -> Prop :=
    sorted0 : sorted A R (listNil A) |
    sorted1 : forall a:A, sorted A R (listCons A a (listNil A)) |
    sortedS : forall (a b:A) (x:list A), R a b -> sorted A R x -> sorted A R (listCons A a (listCons A b x)).

Inductive mirror (A:Set): bintree A -> bintree A -> Prop :=
    mirror0 : mirror A (bintreeNil A) (bintreeNil A) |
    mirrorS : forall (a: A) (x1 x2 y1 y2:bintree A), mirror A x1 y1 -> mirror A x2 y2 -> mirror A (bintreeCons A a x1 x2) (bintreeCons A a y1 y2).

Inductive isomorfo (A:Set): bintree A -> bintree A -> Prop :=
    isomorfo0 : isomorfo A (bintreeNil A) (bintreeNil A) |
    isomorfoS : forall (a b:A) (x y z t:bintree A), isomorfo A x y -> isomorfo A z t -> isomorfo A (bintreeCons A a x z) (bintreeCons A b y t).

Inductive Gtree (A B:Set): Set :=
    leaf : B -> Gtree A B |
    node : A -> forest A B -> Gtree A B
with forest (A B:Set): Set :=
    empty_f : forest A B |
    add_tree : Gtree A B -> forest A B -> forest A B.

End Ejercicio1.

Section Ejercicio2.

Definition Or (p q:bool) : bool :=
    match p with
    | true => true
    | false => q
    end.

Definition And (p q:bool) : bool :=
    match p with
    | true => q
    | false => false
    end.

Definition Not (p:bool) : bool :=
    match p with
    | true => false
    | false => true
    end.

Definition Xor (p q:bool) : bool :=
    match p with
    | true => Not q
    | false => q
    end.

Definition is_nil (A:Set) (l:list A) : bool :=
    match l with
    | listNil _ => true
    | listCons _ _ _ => false
    end.

End Ejercicio2.

Section Ejercicio3.

Fixpoint sum (n m:nat) {struct n} : nat :=
    match n with
    | O => m
    | S k => S (sum k m)
    end.

Fixpoint prod (n m:nat) {struct n} : nat :=
    match n with
    | O => O
    | S k => sum m (prod k m)
    end.

Fixpoint pot (n m:nat) {struct m} : nat :=
    match m with
    | O => S O
    | S k => prod n (pot n k)
    end.

Fixpoint leBool (n m:nat) {struct n} : bool :=
    match n, m with
    | O, _ => true
    | S _, O => false
    | S k, S p => leBool k p
    end.

End Ejercicio3.