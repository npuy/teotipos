(* Nicolas Pereira - 5.139.786-4 *)

Section Ejercicio1.
Variable A B C: Set.

Definition term1_1 : (A->A->A)->A->A := 
  fun (f:A->A->A)(x:A) => f x x.
Check term1_1.

Lemma term1_1_tauto: (A->A->A)->A->A.
Proof.
  tauto.
Qed. 

Lemma term1_1_exact: (A->A->A)->A->A.
Proof.
  exact term1_1.
Qed.

Definition term1_2 : (A->B)->(B->C)->A->B->C :=
  fun (f:A->B)(g:B->C)(x:A)(y:B) => g (f x).
Check term1_2.

Lemma term1_2_tauto : (A->B)->(B->C)->A->B->C.
Proof.
  tauto.
Qed.

Lemma term1_2_exact : (A->B)->(B->C)->A->B->C.
Proof.
  exact term1_2.
Qed.

Definition term1_3 : (A->B)->(A->B->C)->A->C :=
  fun (f:A->B)(g:A->B->C)(a:A) => g a (f a).
Check term1_3.

Lemma term1_3_tauto : (A->B)->(A->B->C)->A->C.
Proof.
  tauto.
Qed.

Lemma term1_3_exact : (A->B)->(A->B->C)->A->C.
Proof.
  exact term1_3.
Qed.

Definition term1_4 : (A->B)->((A->B)->C)->C :=
  fun (f:A->B)(g:(A->B)->C) => g f.
Check term1_4.

Lemma term1_4_tauto : (A->B)->((A->B)->C)->C.
Proof.
  tauto.
Qed.

Lemma term1_4_exact : (A->B)->((A->B)->C)->C.
Proof.
  exact term1_4.
Qed.

End Ejercicio1.


Section Ejercicio2.
Variable A B C: Set.

(*[x:A->B->C][y:A][z:B]((x y)z)*)
Definition term2_1: (A->B->C)->A->B->C :=
  fun (x:A->B->C)(y:A)(z:B) => (x y)z.
Check term2_1.

Definition term2_2: (A->C)->(B->A)->B->C :=
  fun (x:A->C)(y:B->A)(z:B) => x (y z).
Check term2_2.

Definition term2_3: B->(A->B->C)->A->C :=
  fun (z:B) => (fun (x:A->B->C)(y:A) => (x y) z).
Check term2_3.

Definition term2_4:  A->A :=
  (fun (x:A->A) => x) (fun (y:A) => y).
Check term2_4.

End Ejercicio2.


Section Ejercicio3.
Variable A B C: Set.

Definition apply: (A->B)->A->B :=
  fun (f:A->B)(x:A) => f x.
Check apply.

Definition o: (A->B)->(B->C)->(A->C) :=
  fun (f:A->B)(g:B->C) => (fun (x:A) => g (f x)).
Check o.

Definition twice: (A->A)->A->A :=
  fun (f:A->A)(x:A) => f (f x).
Check twice.

Definition applyGen: forall A B : Set, (A->B)->A->B :=
  fun (A:Set)(B:Set)(f:A->B)(x:A) => f x.
Check applyGen.

Definition oGen: forall A B C : Set, (A->B)->(B->C)->(A->C) :=
  fun (A:Set)(B:Set)(C:Set)(f:A->B)(g:B->C) => (fun (x:A) => g (f x)).
Check oGen.

Definition twiceGen: forall A : Set, (A->A)->A->A :=
  fun (A:Set)(f:A->A)(x:A) => f (f x).
Check twiceGen.

End Ejercicio3.


Section Ejercicio4.
Variable A: Set.

Definition id: A->A :=
 fun (x:A) => x.
Check id.

Theorem e4 : forall x:A, (o A A A id id) x = id x.
Proof.
  cbv delta.
  cbv beta.
  reflexivity.
Qed.
Theorem e4_2 : forall x:A, (o A A A id id) x = id x.
Proof.
  compute.
  reflexivity.
Qed.
Theorem e4_3 : forall x:A, (o A A A id id) x = id x.
Proof.
  cbv delta.
  simpl.
  reflexivity.
Qed.

End Ejercicio4.


Section Ejercicio5.

(* 5.1 *)
Definition opI (A : Set) (x : A) := x.

Definition opK (A B : Set) (x : A) (y : B) := x.

Definition opS (A B C : Set) (f : A -> B -> C) (g : A -> B) (x : A) := ((f x) (g x)).

(* 5.2 *)
(* Para formalizar el siguiente lema, determine los tipos ?1 ... ?8 adecuados *)
Lemma e52 : forall A B : Set, opS A (B -> A) A (opK A (B -> A)) (opK A B) = opI A.
Proof.
  cbv delta beta.
  reflexivity.
Qed.

End Ejercicio5.


Section Ejercicio6.
Definition N := forall X : Set, X -> (X -> X) -> X.
Definition Zero (X : Set) (o : X) (f : X -> X) := o.
Definition Uno  (X : Set) (o : X) (f : X -> X) := f (Zero X o f).

(* 6.1 *)
Definition Dos  (X : Set) (o : X) (f : X -> X) := f (Uno X o f).

(* 6.2 *)
Definition Succ (n : N) := fun (X : Set) (o : X) (f : X -> X) => f (n X o f).

Lemma succUno : Succ Uno = Dos.
Proof.
  reflexivity.
Qed.

(* 6.3 *)
Definition Plus (n m : N) : N
                := fun (X : Set) (o : X) (f : X -> X) => n X (m X o f) f.


Infix "++" := Plus (right associativity, at level 60).

Lemma suma1: (Uno ++ Zero) = Uno.
Proof.
  reflexivity.
Qed.

Lemma suma2: (Uno ++ Uno) = Dos.
Proof.
  reflexivity.
Qed.

(* 6.4 *)
Definition Prod (n m : N) : N
                := fun (X:Set) (o:X) (f:X->X) => m X o (fun y:X => n X y f).


Infix "**" := Prod (left associativity, at level 20).

(* 6.5 *)
Lemma prod1 : (Uno ** Zero) = Zero.
Proof.
  reflexivity.
Qed.

Lemma prod2: (Uno ** Dos) = Dos.
Proof.
  reflexivity.
Qed.

End Ejercicio6.


Section Ejercicio7.
(* 7.1 *)
Definition Bool := forall X : Set, X -> X -> X.
Definition t : Bool := fun X x y => x.
Definition f : Bool := fun X x y => y.

(* 7.2 *)
Definition If (b th el : Bool) : Bool :=
  fun X x y => b X (th X x y) (el X x y).

(* 7.3 *)
Definition Not (b : Bool) : Bool :=
  fun X x y => b X y x.

Lemma CorrecNot : (Not t) = f /\ (Not f) = t.
Proof.
  split; reflexivity.
Qed.

(* 7.4 *)
Definition And (a b : Bool) : Bool :=
  If b a f.

Definition And' (a b : Bool) : Bool :=
  fun X x y => a X (b X x y) y.

(* 7.5 *)
Infix "&" := And (left associativity, at level 40).

Lemma CorrecAnd : (t & t) = t /\ (f & t) = f /\ (t & f) = f.
Proof.
  split.
  reflexivity.
  split; reflexivity.
Qed.

End Ejercicio7.



(* Ejercicio8 *)

Section ArrayNat.
Parameter ArrayNat : forall n:nat, Set.
Parameter empty    : ArrayNat 0.
Parameter add      : forall n:nat, nat -> ArrayNat n -> ArrayNat (n + 1).

(* 8.1 *)
Check (add 0 (S 0) empty).
(* ArrayNat (0 + 1). *)

(* 8.2 *)
Check (add 1 0 (add 0 0 empty)).
Check (add 3 0 (add 2 1 (add 1 0 (add 0 1 empty)))).

(* 8.3 *)
Parameter Concat : forall n m:nat, ArrayNat n -> ArrayNat m -> ArrayNat(plus n m).

(* 8.4 *)
Parameter Zip : forall n:nat, ArrayNat n -> ArrayNat n -> (nat -> nat -> nat) -> ArrayNat n.

(* 8.5 *)
Check ArrayNat.

(* 8.6 *)
Parameter ArrayGen : forall (X:Set) (n:nat), Set.
Parameter emptyGen : forall (X:Set), ArrayGen X 0.
Parameter addGen   : forall (X:Set) (n:nat), X -> ArrayGen X n -> ArrayGen X (n + 1).
Parameter ZipGen   : forall (X:Set) (n:nat), ArrayGen X n -> ArrayGen X n -> (X -> X -> X) -> ArrayGen X n.

(* 8.7 *)
Parameter ArrayBool : forall n:nat, ArrayGen bool n.

End ArrayNat.


Section Ejercicio9.

Parameter MatrizNat : forall (n m:nat), Set.

Parameter prod: forall (n m p:nat), MatrizNat n m -> MatrizNat m p -> MatrizNat n p.

Parameter es_id: forall (n:nat), MatrizNat n n -> bool.

Parameter ins_fila: forall (n m:nat), MatrizNat n m -> ArrayNat m -> MatrizNat (n + 1) m.

Parameter ins_columna: forall (n m:nat), MatrizNat n m -> ArrayNat n -> MatrizNat n (m + 1).

Check MatrizNat.

End Ejercicio9.


Section Ejercicio10.

Parameter Array : Set -> nat -> Set.
Parameter emptyA : forall X : Set, Array X 0.
Parameter addA : forall (X : Set) (n : nat), X -> Array X n -> Array X (S n).

Parameter Matrix : Set -> nat -> Set.
Parameter emptyM : forall X : Set, Matrix X 0.
Parameter addM : forall (X : Set) (n : nat), Matrix X n -> Array X (S n) -> Matrix X (S n).

Definition A1 := addA nat 0 1 (emptyA nat).
Definition M1 := addM nat 0 (emptyM nat) A1. (* matriz de una columna *)
Definition A2 := addA nat 1 2 (addA nat 0 2 (emptyA nat)).
Definition M2 := addM nat 1 M1 A2. (* matriz de dos columnas *) 
Definition A3 := addA nat 2 3 (addA nat 1 3 (addA nat 0 3 (emptyA nat))).
Definition M3 := addM nat 2 M2 A3. (* matriz de tres columnas *)

Check M3.

End Ejercicio10.

Section Ejercicio11.

Parameter ABNat : forall n : nat, Set.

Parameter emptyAB : ABNat 0.

Parameter addAB : forall n : nat, nat -> ABNat n -> ABNat n -> ABNat (S n).

Definition AB2 := addAB 1 3 (addAB 0 7 emptyAB emptyAB) (addAB 0 7 emptyAB emptyAB).
Check AB2.

Parameter ABGen : forall (X:Set) (n:nat), Set.
Parameter emptyABGen : forall (X:Set), ABGen X 0.
Parameter addABGen : forall (X:Set) (n:nat), X -> ABGen X n -> ABGen X n -> ABGen X (S n).

End Ejercicio11.


Section Ejercicio12.

Parameter AVLNat : forall n:nat, Set.
Parameter emptyAVL : AVLNat 0.
Parameter addAVL1 : forall n:nat, nat -> AVLNat n -> AVLNat n -> AVLNat (S n).
Parameter addAVL2 : forall n:nat, nat -> AVLNat (S n) -> AVLNat n -> AVLNat (S (S n)).
Parameter addAVL3 : forall n:nat, nat -> AVLNat n -> AVLNat (S n) -> AVLNat (S (S n)).

Definition arbolAVL := addAVL2 0 2 (addAVL1 0 1 emptyAVL emptyAVL) emptyAVL.
Check arbolAVL.

Parameter AVLGen : forall (X:Set) (n:nat), Set.
Parameter emptyAVLGen : forall X:Set, AVLGen X 0.
Parameter addAVLGen1 : forall (X:Set) (n:nat), X -> AVLGen X n -> AVLGen X n -> AVLGen X (S n).
Parameter addAVLGen2 : forall (X:Set) (n:nat), X -> AVLGen X (S n) -> AVLGen X n -> AVLGen X (S (S n)).
Parameter addAVLGen3 : forall (X:Set) (n:nat), X -> AVLGen X n -> AVLGen X (S n) -> AVLGen X (S (S n)).

End Ejercicio12.


Section Ejercicio13.
Variable A B C: Set.

Lemma e13_1 : (A -> B -> C) -> B -> A -> C.
Proof.
  exact (fun (f:A->B->C)(b:B)(a:A) => f a b).
Qed.

Lemma e13_2 : (A -> B) -> (B -> C) -> A -> C.
Proof.
  exact (fun (f:A->B)(g:B->C)(a:A) => g (f a)).
Qed.

Lemma e13_3 : (A -> B -> C) -> (B -> A) -> B -> C.
Proof.
  exact (fun (f:A->B->C)(g:B->A)(b:B) => f (g b) b).
Qed.

End Ejercicio13.


Section Ejercicio14.
Variable A B C: Prop.

Lemma Ej314_1 : (A -> B -> C) -> A -> (A -> C) -> B -> C.
Proof.
  intros f a g b.
  exact (g a).
Qed.

Lemma Ej314_2 : A -> ~ ~ A.
Proof.
  unfold not.
  intros.
  exact (H0 H).
Qed.

Lemma Ej314_3 : (A -> B -> C) -> A -> B -> C.
Proof.
  exact (fun (f:A->B->C)(a:A)(b:B) => f a b).
Qed.

Lemma Ej314_4 : (A -> B) -> ~ (A /\ ~ B).
Proof.
  unfold not.
  intros.
  elim H0; intros.
  exact (H2 (H H1)).
Qed.

End Ejercicio14.



Section Ejercicio15.

Variable U : Set.
Variable e : U.
Variable A B : U -> Prop.
Variable P : Prop.
Variable R : U -> U -> Prop.

Lemma Ej315_1 : (forall x : U, A x -> B x) -> (forall x : U, A x) ->
forall x : U, B x.
Proof.
  intros.
  exact (H x (H0 x)).
Qed.

Lemma Ej315_2 : forall x : U, A x -> ~ (forall x : U, ~ A x).
Proof.
  unfold not.
  intros.
  exact (H0 x H).
Qed.

Lemma Ej315_3 : (forall x : U, P -> A x) -> P -> forall x : U, A x.
Proof.
  exact (fun (H:(forall x:U, P -> A x))(p:P)(x:U) => H x p).
Qed.

Lemma Ej315_4 : (forall x y : U, R x y) -> forall x : U, R x x.
Proof.
  exact (fun (H:(forall x y : U, R x y))(x:U) => H x x).
Qed.

Lemma Ej315_5 : (forall x y: U, R x y -> R y x) ->
                 forall z : U, R e z -> R z e.
Proof.
  exact (fun (H:(forall x y : U, R x y -> R y x))(z:U) => H e z).
Qed.

End Ejercicio15.
