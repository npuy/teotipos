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

Section Ejercicio4.

Fixpoint length (A:Set) (l:list A) {struct l} : nat :=
    match l with
    | listNil _ => O
    | listCons _ _ k => S (length A k)
    end.

Fixpoint append (A:Set) (l k:list A) {struct l} : list A :=
    match l with
    | listNil _ => k
    | listCons _ x lr => listCons A x (append A lr k)
    end.

Fixpoint reverseAux (A:Set) (l ret:list A) {struct l} : list A :=
    match l with
    | listNil _ => ret
    | listCons _ x lr => reverseAux A lr (listCons A x ret)
    end.
Definition reverse (A:Set) (l:list A) : list A :=
    reverseAux A l (listNil A).

Fixpoint filter (A:Set) (f:A->bool) (l:list A) {struct l} : list A :=
    match l with
    | listNil _ => listNil A
    | listCons _ x lr => 
        match (f x) with
        | true => listCons A x (filter A f lr)
        | false => filter A f lr
        end
    end.

Fixpoint map (A B:Set) (f:A->B) (l:list A) {struct l} : list B :=
    match l with
    | listNil _ => listNil B
    | listCons _ x lr => listCons B (f x) (map A B f lr)
    end.

Fixpoint exists_ (A:Set) (f:A->bool) (l:list A) {struct l} : bool :=
    match l with
    | listNil _ => false
    | listCons _ x lr =>
        match (f x) with
        | true => true
        | false => exists_ A f lr
        end
    end.

End Ejercicio4.

Section Ejercicio5.

Fixpoint inverse (A:Set) (b:bintree A) {struct b} : bintree A :=
    match b with
    | bintreeNil _ => bintreeNil A
    | bintreeCons _ x b1 b2 => bintreeCons A x (inverse A b2) (inverse A b1)
    end.

Fixpoint countExt (A B:Set) (t:Gtree A B) : nat :=
    match t with
    | leaf _ _ _ => S O
    | node _ _ _ f => countExtF A B f
    end
with countExtF (A B:Set) (f:forest A B) : nat :=
    match f with
    | empty_f _ _ => O
    | add_tree _ _ t1 f1 => sum (countExt A B t1) (countExtF A B f1)
    end.

Fixpoint countInt (A B:Set) (t:Gtree A B) : nat :=
    match t with
    | leaf _ _ _ => O
    | node _ _ _ f => S (countIntF A B f)
    end
with countIntF (A B:Set) (f:forest A B) : nat :=
    match f with
    | empty_f _ _ => O
    | add_tree _ _ t1 f1 => sum (countInt A B t1) (countIntF A B f1)
    end.

Definition intGtExt (A B:Set) (t:Gtree A B) : bool := 
    Not (leBool (countInt A B t) (countExt A B t)).

End Ejercicio5.

Section Ejercicio6.

Definition listN := list nat.

Fixpoint eqBool (n m:nat) {struct n} : bool :=
    match n, m with
    | O, O => true
    | S n1, S m1 => eqBool n1 m1
    | _, _ => false
    end.
Definition member (n:nat) (l:listN) : bool :=
    exists_ nat (eqBool n) l.

Definition delete (l:listN) (n:nat) : listN :=
    filter nat (fun x => Not (eqBool n x)) l.

Fixpoint insert (n:nat) (l:listN) : listN :=
    match l with
    | listNil _ => listCons nat n (listNil nat)
    | listCons _ m l1 =>
        match (leBool n m) with
        | false => listCons nat m (insert n l1)
        | true => listCons nat n l
        end
    end.

Fixpoint insert_sort (l:listN) : listN :=
    match l with
    | listNil _ => listNil nat
    | listCons _ n l1 => insert n (insert_sort l1)
    end.

Definition memberG (A:Set) (eqA:A->A->bool) (a:A) (l:list A) : bool :=
    exists_ A (eqA a) l.
    
Definition deleteG (A:Set) (eqA:A->A->bool) (l:list A) (a:A) : list A :=
    filter A (fun x => Not (eqA a x)) l.

Fixpoint insertG (A:Set) (leBool:A->A->bool) (n:A) (l:list A) : list A :=
    match l with
    | listNil _ => listCons A n (listNil A)
    | listCons _ m l1 =>
        match (leBool n m) with
        | false => listCons A m (insertG A leBool n l1)
        | true => listCons A n l
        end
    end.

Fixpoint insert_sortG (A:Set) (leBool:A->A->bool) (l:list A) : list A :=
    match l with
    | listNil _ => listNil A
    | listCons _ n l1 => insertG A leBool n (insert_sortG A leBool l1)
    end.

End Ejercicio6.

Section Ejercicio7.

Inductive Exp (A:Set) : Set :=
| ato : A -> Exp A
| mas : Exp A -> Exp A -> Exp A
| mul : Exp A -> Exp A -> Exp A
| ide : Exp A -> Exp A
.

Fixpoint eval (e:Exp nat) : nat :=
    match e with
    | ato _ a => a
    | mas _ a b => sum (eval a) (eval b)
    | mul _ a b => prod (eval a) (eval b)
    | ide _ a => eval a
    end.

Fixpoint evalBool (e:Exp bool) : bool :=
    match e with
    | ato _ a => a
    | mas _ a b => Or (evalBool a) (evalBool b)
    | mul _ a b => And (evalBool a) (evalBool b)
    | ide _ a => Not (evalBool a)
    end.

(* (2 + 3) * 4  -> deberia dar 20 *)
Compute eval (mul nat (mas nat (ato nat 2) (ato nat 3)) (ato nat 4)).

(* - (true * false) + false -> (not (true and false)) or false -> deberia dar true   *) 
Compute evalBool (mas bool (ide bool (mul bool (ato bool true) (ato bool false))) (ato bool false)).

End Ejercicio7.

Section Ejercicio8.

Theorem test_conmutatividad_and :
    forall a b:bool, And a b = And b a.
Proof.
    destruct a;
    destruct b;
    reflexivity.
Qed.

Theorem test_conmutatividad_or :
    forall a b:bool, Or a b = Or b a.
Proof.
    destruct a;
    destruct b;
    reflexivity.
Qed.

Theorem test_asociatividad_and :
    forall a b c:bool, And (And a b) c = And a (And b c).
Proof.
    destruct a;
    destruct b;
    destruct c;
    reflexivity.
Qed.

Theorem test_asociatividad_or :
    forall a b c:bool, Or (Or a b) c = Or a (Or b c).
Proof.
    destruct a;
    destruct b;
    destruct c;
    reflexivity.
Qed.

Theorem LAnd : 
    forall a b : bool, And a b = true <-> a = true /\ b = true.
Proof.
    destruct a;
    destruct b;
    unfold iff;
    split;
    intro h;
    (
        split;
        assumption + reflexivity
    ) + apply h.
    (* - split; assumption.
    - apply h.
    - split. reflexivity. assumption. 
    - apply h.
    - split. assumption. reflexivity.
    - apply h.
    - split; assumption.
    - apply h. *)
Qed.

Theorem LOr1 :
    forall a b : bool, Or a b = false <-> a = false /\ b = false.
Proof.
    destruct a;
    destruct b;
    unfold iff;
    split;
    intro h;
    (
        split;
        assumption + reflexivity
    ) + apply h.
Qed.

Theorem LOr2 :
    forall a b : bool, Or a b = true <-> a = true \/ b = true.
Proof.
    destruct a;
    destruct b;
    unfold iff;
    split;
    intro h;
    (
        left + right; assumption + reflexivity
    ) + reflexivity + (
        elim h; intro h1; assumption
    ).
    (* - left + right; assumption + reflexivity.
    - reflexivity. 
    - left + right; assumption + reflexivity.
    - reflexivity.
    - left + right; assumption + reflexivity.
    - reflexivity.
    - left + right; assumption + reflexivity.
    - elim h; intro h1; assumption. *)
Qed.

Theorem LXor :
    forall a b : bool, Xor a b = true <-> a <> b.
Proof.
    intros a b.
    case a;
    unfold iff;
    split; case b; simpl; intro h;
    discriminate h + discriminate + reflexivity + (elim h; reflexivity).
    (* - discriminate h.
    - discriminate.
    - elim h. reflexivity.
    - reflexivity.
    - discriminate.
    - discriminate h.
    - reflexivity.
    - elim h. reflexivity. *)
Qed.

Theorem LNot :
    forall b : bool, Not (Not b) = b.
Proof.
    destruct b;
    reflexivity.
Qed.

End Ejercicio8.

Section Ejercicio9.
(* 
Ejercicio 4.9.  Demuestre las siguientes propiedades de la suma, 
definida en el ejercicio 4.3:  
1. SumO : forall n : nat, sum n 0 = n /\ sum 0 n = n  
2. SumS : forall n m : nat, sum n (S m) = sum (S n) m  
3. SumAsoc : forall n m p : nat, sum n (sum m p) = sum (sum n m) p 
4. SumConm : forall n m : nat, sum n m = sum m n 
*)

Theorem SumO : forall n : nat, sum n 0 = n /\ sum 0 n = n.
Proof.
  intro n; split.
  - induction n as [| k IH].
    + reflexivity.
    + simpl.
      rewrite IH.
      reflexivity.
  - reflexivity.
Qed.

Theorem SumS : forall n m : nat, sum n (S m) = sum (S n) m.
Proof.
  intros n m.
  induction n as [| k IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Theorem SumAsoc : forall n m p : nat, sum n (sum m p) = sum (sum n m) p.
Proof.
  intros n m p.
  induction n as [| k IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Theorem SumConm : forall n m : nat, sum n m = sum m n.
Proof.
  intros n m.
  induction n as [| k IH].
  - simpl.
    symmetry.
    apply (SumO m).
  - simpl.
    rewrite IH.
    rewrite SumS.
    reflexivity.
Qed.

End Ejercicio9.