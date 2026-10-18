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
    mirrorS : forall (a: A) (x1 x2 y1 y2:bintree A), mirror A x1 y2 -> mirror A x2 y1 -> mirror A (bintreeCons A a x1 x2) (bintreeCons A a y1 y2).

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

Section Ejercicio10.
(* 
Ejercicio 4.10. Demuestre las siguientes propiedades de la suma y el producto, definidos en el ejercicio 4.3:  
1.  ProdConm : forall n m : nat, prod n m = prod m n 
2.  ProdAsoc : forall n m p : nat, prod n (prod m p) = prod (prod n m) p 
3.  ProdDistr : forall n m p : nat, prod n (sum m p) = sum (prod n m) (prod n p) 
*)

Lemma prod_n_0 : forall n : nat, prod n 0 = 0.
Proof.
  induction n as [| k IH].
  - reflexivity.
  - simpl. assumption.
Qed.

Lemma prod_n_Sm : forall n m : nat, prod n (S m) = sum n (prod n m).
Proof.
  intros n m.
  induction n as [| k IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    rewrite (SumAsoc m k).
    rewrite (SumAsoc k m).
    rewrite (SumConm m k).
    reflexivity.
Qed.

Theorem ProdConm : forall n m : nat, prod n m = prod m n.
Proof.
  intros n m.
  induction n as [| k IH].
  - simpl.
    rewrite prod_n_0.
    reflexivity.
  - simpl.
    rewrite prod_n_Sm.
    rewrite IH.
    reflexivity.
Qed.

Lemma prod_factor : forall n m p : nat, prod (sum n m) p = sum (prod n p) (prod m p).
Proof.
  intros n m p.
  induction n as [| k IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    rewrite SumAsoc.
    reflexivity.
Qed.

Theorem ProdAsoc : forall n m p : nat, prod n (prod m p) = prod (prod n m) p.
Proof.
  intros n m p.
  induction n as [| k IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    rewrite prod_factor.
    reflexivity.
Qed.

Theorem ProdDistr : forall n m p : nat, prod n (sum m p) = sum (prod n m) (prod n p).
Proof.
  intros n m p.
  rewrite (ProdConm n (sum m p)).
  rewrite (ProdConm n m).
  rewrite (ProdConm n p).
  apply prod_factor.
  (* intros n m p.
  induction n as [| k IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    rewrite (SumAsoc (sum m p) (prod k m) (prod k p)).
    rewrite <- (SumAsoc m p (prod k m)).
    rewrite (SumConm p (prod k m)).
    rewrite (SumAsoc m (prod k m) p).
    rewrite <- (SumAsoc (sum m (prod k m)) p (prod k p)).
    reflexivity. *)
Qed.

End Ejercicio10.

Section Ejercicio11.
(*
Ejercicio 4.11.  Demuestre las siguientes propiedades de las funciones definidas en el 
ejercicio 4.4 (no escribimos el parámetro A para hacer más fácil la lectura):  
1. L1 : forall (A : Set) (l : list A), append A l (nil A) = l   
2. L2 : forall (A : Set) (l : list A) (a : A), ~(cons A a l) = nil A 
3. L3 : forall (A : Set) (l m : list A) (a : A), cons A a (append A l m) = append A (cons A a l) m 
4. L4 : forall (A : Set) (l m : list A), length A (append A l m) = sum (length A l) (length A m)  
5. L5 : forall (A : Set) (l : list A), length A (reverse A l) = length A l
*)

Theorem L1 : forall (A : Set) (l : list A), append A l (listNil A) = l.
Proof.
  intros A l.
  induction l as [| a r HI].
  - reflexivity.
  - simpl.
    rewrite HI.
    reflexivity.
Qed.

Theorem L2 : forall (A : Set) (l : list A) (a : A), ~(listCons A a l) = listNil A.
Proof.
  intros A l a.
  discriminate.
Qed.

Theorem L3 : forall (A : Set) (l m : list A) (a : A), listCons A a (append A l m) = append A (listCons A a l) m.
Proof.
  intros A l m a.
  simpl.
  reflexivity.
Qed.

Theorem L4 : forall (A : Set) (l m : list A), length A (append A l m) = sum (length A l) (length A m).
Proof.
  intros A l m.
  induction l as [| a k HI].
  - reflexivity.
  - simpl.
    rewrite HI.
    reflexivity.
Qed.

Lemma l5_1: forall (A : Set) (l acc : list A), length A (reverseAux A l acc) = sum (length A l) (length A acc).
Proof.
  intros A l.
  induction l as [| a r HI]; intro acc.
  - reflexivity.
  - simpl.
    rewrite HI.
    simpl.
    rewrite SumS.
    reflexivity.
Qed.

Theorem L5 : forall (A : Set) (l : list A), length A (reverse A l) = length A l.
Proof.
  intros A l.
  unfold reverse.
  rewrite l5_1.
  simpl.
  apply SumO.
Qed.

End Ejercicio11.

Section Ejercicio12.
(* 
Ejercicio 4.12.  Demuestre las siguientes propiedades de las funciones definidas en el ejercicio 4.4:  
1. L7 : forall (A B : Set) (l m : list A) (f : A -> B),  map A B f (append A l m) = append B (map A B f l) (map A B f m). 
2. L8 : forall (A : Set) (l m : list A) (P : A -> bool), filter A P (append A l m) = append A (filter A P l) (filter A P m)  
3. L9 : forall (A : Set) (l : list A) (P : A -> bool), filter A P (filter A P l) = filter A P l  
4. L10 : forall (A : Set) (l m n : list A), append A l (append A m n) = append A (append A l m) n 
*)

Theorem L7 : forall (A B : Set) (l m : list A) (f : A -> B),  map A B f (append A l m) = append B (map A B f l) (map A B f m). 
Proof.
  intros A B l m f.
  induction l as [| a r HI].
  - reflexivity.
  - simpl.
    rewrite HI.
    reflexivity.
Qed.

Lemma l8_1 : forall (A : Set) (P : A -> bool), filter A P (listNil A) = listNil A.
Proof.
  reflexivity.
Qed.

Theorem L8 : forall (A : Set) (l m : list A) (P : A -> bool), filter A P (append A l m) = append A (filter A P l) (filter A P m).
Proof.
  intros A l m P.
  induction l as [| a r HI].
  - reflexivity.
  - simpl.
    destruct (P a).
    + rewrite HI. reflexivity.
    + rewrite HI. reflexivity.
Qed.

Theorem L9 : forall (A : Set) (l : list A) (P : A -> bool), filter A P (filter A P l) = filter A P l.
Proof.
  intros A l.
  induction l as [| a r HI];
  intro P.
  - reflexivity.
  - simpl.
    destruct (P a) eqn:Ha.
    + simpl.
      rewrite Ha.
      rewrite HI.
      reflexivity.
    + rewrite HI. reflexivity.
Qed.

Theorem L10 : forall (A : Set) (l m n : list A), append A l (append A m n) = append A (append A l m) n.
Proof.
  intros A l m n.
  induction l as [| a r HI].
  - reflexivity.
  - simpl.
    rewrite HI.
    reflexivity.
Qed.

End Ejercicio12.

Section Ejercicio13.
(*
Ejercicio 4.13.  Considere  la  siguiente  función  definida  sobre  listas  de  elementos  de  un  tipo genérico: 
Fixpoint filterMap (A B : Set) (P : B -> bool) (f : A -> B)     (l : list A) {struct l} : list B :=     match l with     | nil => nil B     | cons a l1 =>         match P (f a) with         | true => cons B (f a) (filterMap A B P f l1)         | false => filterMap A B P f l1        end    end.    
Pruebe el siguiente lema: 
Lemma FusionFilterMap : forall (A B : Set) (P : B -> bool) (f : A -> B) (l : list A), 
  filter B P (map A B f l) = filterMap A B P f l. 
Donde las funciones filter y map son las definidas en el ejercicio 4.4.
*)
Fixpoint filterMap (A B : Set) (P : B -> bool) (f : A -> B) (l : list A) {struct l} : list B :=
  match l with
  | listNil _ => listNil B
  | listCons _ a l1 =>
    match P (f a) with
    | true => listCons B (f a) (filterMap A B P f l1)
    | false => filterMap A B P f l1
    end
  end.    

Lemma FusionFilterMap : forall (A B : Set) (P : B -> bool) (f : A -> B) (l : list A), 
  filter B P (map A B f l) = filterMap A B P f l. 
Proof.
  intros A B P f l.
  induction l as [| a r HI].
  - reflexivity.
  - simpl.
    destruct (P (f a)).
    + rewrite HI. reflexivity.
    + rewrite HI. reflexivity.
Qed.

End Ejercicio13.

Section Ejercicio14.
(* Ejercicio 4.14.  Demuestre que la función inverse del ejercicio 4.5 da como resultado un árbol 
que  cumple  con  la  propiedad  de  ser  espejo  del  dado  (utilice  la  definición  de  espejo  del 
ejercicio 4.1).  *)

Theorem inverse_mirror : forall (A : Set) (t : bintree A), mirror A t (inverse A t).
Proof.
  intros A t.
  induction t as [| a l HIl r HIr].
  - simpl.
    apply mirror0.
  - simpl.
    apply mirrorS;
    assumption.
Qed.

End Ejercicio14.

Section Ejercicio15.
(* Ejercicio 4.15.
1. Demuestre que la función identidad para árboles binarios de elementos de un tipo genérico 
da como resultado un árbol que cumple con la propiedad de ser isomorfo del dado. 
2. Pruebe que la relación de isomorfismo entre árboles binarios es reflexiva y simétrica. 
Utilice la definición de isomorfo del ejercicio 4.1.  *)

Fixpoint idTree (A : Set) (t : bintree A) : bintree A :=
  match t with
  | bintreeNil _ => bintreeNil A
  | bintreeCons _ a l r => bintreeCons A a (idTree A l) (idTree A r)
  end.

Theorem isomorfo_identidad : forall (A : Set) (t : bintree A), isomorfo A t (idTree A t).
Proof.
  intros A t.
  induction t as [| a l HIl r HIr].
  - simpl. apply isomorfo0.
  - simpl.
    apply isomorfoS;
    assumption.
Qed.

End Ejercicio15.

Section Ejercicio16.
(* Ejercicio 4.16. 
Defina el tipo de datos Tree que representa árboles binarios de elementos de un 
tipo  genérico  que  sólo  guarda  información  en  los  nodos  hojas  (nodos  externos).  Los  nodos 
internos no guardan información. El árbol más pequeño es una hoja. 
1. Defina una función mapTree que dado un árbol de tipo (Tree A), para un tipo genérico A, 
y una función f:A->B, con B un Set dado, retorne un árbol de tipo (Tree B) obtenido por  
la aplicación de la función f a cada uno de los nodos hojas del árbol parámetro. 
2. Defina  una  función  que  cuente  la  cantidad  de  nodos  hojas  que  posee  un  árbol  de  tipo  
(Tree A), para un tipo genérico A. 
3. Pruebe que la función MapTree preserva la cantidad de nodos hojas del árbol parámetro. 
4. Defina una función hojas que retorne una lista con las hojas de un árbol de tipo (Tree A), 
para un tipo genérico A. Pruebe luego que la cantidad de nodos hojas que posee un árbol de 
tipo  (Tree  A),  para  un  tipo  genérico  A,  es  igual  a  la  longitud  de  la  lista  resultante  de 
aplicarle la función hojas al árbol. *)

End Ejercicio16.

Section Ejercicio17.
(* Ejercicio 4.17.  
1. Defina  inductivamente  una  relación  binaria  posfijo  entre  listas  de  elementos  de  un  tipo 
genérico, tal que una lista l1 se relaciona con una lista l2 si y sólo si l1 es un posfijo de l2 
(notación:  l1 « l2). Más formalmente, l1 « l2  sii  l2 = l3++l1, para alguna lista l3, donde 
++ representa la concatenación de listas (append).  
2. Defina la función ++ entre listas de elementos de un tipo  genérico  y  pruebe la  corrección 
de la relación posfijo del ejercicio anterior demostrando que: 
2.1. para todas listas l1, l2 y l3:  Si l2 = l3++l1 entonces l1 « l2. 
2.2. para todas listas l1, l2: Si l1 « l2 entonces existe una lista l3 tal que l2 = l3++l1. 
2.3. Pruebe que para todas listas l1, l2 y l3 se cumple que l2 « l1++l2. 
3. Defina  una  función  último  que  dada  una  lista  de  elementos  de  un  tipo  genérico  retorne  la 
lista  que  contiene  a  su  último  elemento.  Si  la  lista  parámetro  es  vacía,  la  función  último 
retorna la lista vacía.  
4. Pruebe que la función último de una lista es un posfijo de dicha lista. *)

(* 17.1. *)
Inductive posfijo (A:Set) : list A -> list A -> Prop :=
  | posfijo0 : forall (l : list A), posfijo A l l
  | posfijo1 : forall (a : A) (l m : list A), posfijo A l m -> posfijo A l (listCons A a m).

Lemma posfijo_nil : forall (A:Set) (l : list A), posfijo A (listNil A) l.
Proof.
  intros A l.
  induction l as [| a r HI].
  - apply posfijo0.
  - apply posfijo1.
    assumption.
Qed.

(* 17.2.3. *)
Theorem posfijo_l : forall (A:Set) (l m : list A), posfijo A l (append A m l).
Proof.
  intros A l m.
  induction m.
  - simpl. apply posfijo0.
  - simpl. apply posfijo1. assumption.
Qed.

(* 17.2.1 *)
Theorem posfijo_append : forall (A:Set) (l1 l2 l3 : list A), l2 = (append A l3 l1) -> posfijo A l1 l2.
Proof.
  intros A l1 l2 l3 H.
  rewrite H.
  apply posfijo_l.
Qed.

(* 17.2.2 *)
Theorem posfijo_exist_l3 : forall (A:Set) (l1 l2 : list A), 
  posfijo A l1 l2 -> exists (l3: list A), l2 = (append A l3 l1).
Proof.
  intros A l1 l2 H.
  induction H as [| a l1 l2 H IH].
  - exists (listNil A).
    reflexivity.
  - elim IH.
    intros l3 H1.
    exists (listCons A a l3).
    simpl.
    rewrite H1.
    reflexivity.
Qed.

(* 17.3 *)
Fixpoint ultimo (A:Set) (l:list A) : list A :=
  match l with
  | listNil _ => listNil A
  | listCons _ a (listNil _) => l
  | listCons _ a r => ultimo A r
  end.

(* 17.4 *)
Theorem posfijo_ultimo : forall (A:Set) (l:list A), posfijo A (ultimo A l) l.
Proof.
  intros A l.
  induction l as [| a r HI].
  - simpl. apply posfijo0.
  - simpl.
    destruct r.
    + apply posfijo0.
    + apply posfijo1.
      assumption.
Qed.

End Ejercicio17.

Section Ejercicio20.

(* 20.1 *)
Inductive ACom (A:Set) : nat -> Set :=
  | AComNil : A -> ACom A 0
  | AComCons : forall (n:nat), A -> ACom A n -> ACom A n -> ACom A (S n).

(* 20.2 *)
Fixpoint h (A:Set) (n:nat) (t:ACom A n) : nat :=
  match t with
  | AComNil _ _ => S 0
  | AComCons _ m _ l r => sum (h A m l) (h A m r)
  end.

(* Parameter pot: nat -> nat -> nat. *)
Axiom potO : forall n : nat, pot (S n) 0 = 1.
(*  n0 = 1   forall n>0  *)
Axiom potS : forall m: nat, pot 2 (S m) = sum (pot 2 m) (pot 2 m).
(*  2m+1 = 2m + 2m  *)

(* 20.3 *)
Theorem h_2n : forall (A:Set) (n:nat) (t:ACom A n), h A n t = pot 2 n.
Proof.
  intros A n t.
  induction t as [| t a l IHl r IHr].
  - reflexivity.
  - rewrite potS.
    simpl.
    rewrite IHl.
    rewrite IHr.
    reflexivity.
Qed.

End Ejercicio20.

Section Ejercicio21.
(* Ejercicio 4.21.  
1. Defina inductivamente la familia de conjuntos sobre los naturales AB de árboles binarios 
de altura n y elementos de un tipo genérico A (la altura del árbol vacío es 0).

2. Defina  una  función  camino  que,  para  todo  n:nat  retorne  una  lista  con  el  camino  más 
largo de un árbol de tipo (AB A n), con A el tipo genérico de los elementos del árbol. Si 
hay  más  de  un  camino  más  largo,  la  función  debe  retornar  el  camino  de  más  a  la 
izquierda de ellos. El camino debe comenzar con el nodo de la raíz del árbol  y finalizar 
con  una  hoja.  Si  el  árbol  es  vacío,  camino  debe  retornar  la  lista  vacía.  La  función 
camino debe recorrer, en el cómputo, sólo un camino del árbol. 

3.  Pruebe  que  la  función  camino,  dado  un  árbol  de  tipo  (AB A n)  retorna  una  lista  de 
largo igual a n. *)

(* 21.1 *)
Inductive AB (A:Set) : nat -> Set :=
  | nilAB : AB A O
  | consABl : forall (n m:nat), leq m n -> A -> AB A n -> AB A m -> AB A (S n)
  | consABr : forall (n m:nat), leq (S n) m -> A -> AB A n -> AB A m -> AB A (S m).

(* 21.2 *)
Fixpoint camino (A:Set) (n:nat) (t:AB A n) : list A :=
  match t with
  | nilAB _ => listNil A
  | consABl _ n' m' _ a l _ => listCons A a (camino A n' l)
  | consABr _ n' m' _ a _ r => listCons A a (camino A m' r)
  end.

(* 22.3 *)
Theorem camino_length : forall (A:Set) (n:nat) (t: AB A n), length A (camino A n t) = n.
Proof.
  intros A n t.
  induction t as [| n' m' Hl a l HIl r HIr | n' m' Hl a l HIl r HIr].
  - reflexivity.
  - simpl. rewrite HIl. reflexivity.
  - simpl. rewrite HIr. reflexivity.
Qed.

End Ejercicio21.