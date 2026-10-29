Section Ejercicio1.
(* Ejercicio 5.1.  Considere las siguientes relaciones inductivas:  
 Inductive LE : nat -> nat -> Prop :=   
 | Le_O : forall n : nat, LE 0 n   
 | Le_S : forall n m : nat, LE n m -> LE (S n) (S m).   
 Inductive Mem (A : Set) (a : A) : list A -> Prop :=   
 | here : forall x : list A, Mem A a (cons A a x)   
 | there : forall x : list A, Mem A a x ->  forall b : A, Mem A a (cons A b x).   
 Demuestre los siguientes resultados usando las tácticas de inversión:  
 1.  Theorem not_sn_le_o: forall n:nat, ~ LE (S n) O. 
 2.  Theorem  nil_empty: forall a:A, ~ Mem a (nil A). 
 3.  4 no es menor o igual que 3. 
 4.  Para todo natural n, el sucesor de n no es menor o igual que n. 
 5.  La relación menor o igual (LE) es transitiva. 
 6.  Si un elemento pertenece a una lista, entonces pertenece a la concatenación de esta lista 
con cualquier otra.  *)

Inductive LE : nat -> nat -> Prop :=   
  | Le_O : forall n : nat, LE 0 n   
  | Le_S : forall n m : nat, LE n m -> LE (S n) (S m).   

Inductive Mem (A : Set) (a : A) : list A -> Prop :=   
  | here : forall x : list A, Mem A a (@cons A a x)
  | there : forall x : list A, Mem A a x ->  forall b : A, Mem A a (@cons A b x).

(* 1.1. *)
Theorem not_sn_le_o: forall n:nat, ~ LE (S n) O.
Proof.
  intros n H.
  inversion H.
Qed.

(* 1.2. *)
Theorem nil_empty: forall (A:Set) (a:A), ~ Mem A a (@nil A).
Proof.
  intros A a H.
  inversion H.
Qed.

(* 1.3. *)
Theorem not_4_LE_3: ~ (LE 4 3).
Proof.
  intro H.
  inversion_clear H as [| x y H1].
  inversion_clear H1 as [| x y H2].
  inversion_clear H2 as [| x y H3].
  inversion_clear H3.
Qed.

(* 1.4. *)
Theorem not_sn_le_n: forall n:nat, ~ LE (S n) n.
Proof.
  intros n H.
  induction n.
  - inversion H.
  - inversion H.
    elim IHn.
    assumption.
Qed.

(* 1.5. *)
Theorem trans_le: forall a b c:nat, LE a b /\ LE b c -> LE a c.
Proof.
  intros a b c [H1 H2]. revert c H2.
  induction H1 as [n | n m H IH]; intros c H2.
  - apply Le_O.
  - inversion H2 as [| m' c' Hmc]. subst.
    apply Le_S. apply IH. assumption.
Qed.
(* Proof.
  induction a; intros b c [H1 H2].
  - apply Le_O.
  - inversion H1 as [| a' m Ham]. subst.
    inversion H2 as [| m' c' Hmc]. subst.
    apply Le_S.
    apply (IHa m c'). split; assumption.
Qed. *)

(* 1.6. *)
Theorem mem_concat: forall (A : Set) (a : A) (l1 l2 : list A), Mem A a l1 -> Mem A a (l1 ++ l2).
Proof.
  intros A a l1 l2 H.
  induction H.
  - simpl. apply here.
  - simpl. apply there. assumption.
Qed.

End Ejercicio1.

Section Ejercicio2.
(* 
Ejercicio 5.2.  Considere las definiciones de árboles binarios, isomorfismo entre árboles binarios 
y la función que retorna el árbol espejo de uno dado del práctico anterior. Pruebe las siguientes 
propiedades: 
1.  El árbol vacío no es isomorfo a ningún árbol no vacío (con al menos un nodo). 
2.  Si dos árboles no vacíos son isomorfos, entonces también lo son sus subárboles 
izquierdos y derechos, respectivamente. 
3.  La relación de isomorfismo entre árboles binarios es transitiva. 
4.  Si dos árboles binarios son isomorfos, también los son sus árboles espejos.   
*)

Inductive bintree (A:Set): Set :=
    bintreeNil : bintree A |
    bintreeCons : A -> bintree A -> bintree A -> bintree A.

Inductive isomorfo (A:Set): bintree A -> bintree A -> Prop :=
    isomorfo0 : isomorfo A (bintreeNil A) (bintreeNil A) |
    isomorfoS : forall (a b:A) (x y z t:bintree A), isomorfo A x y -> isomorfo A z t -> isomorfo A (bintreeCons A a x z) (bintreeCons A b y t).

Fixpoint espejo (A:Set) (b:bintree A) {struct b} : bintree A :=
    match b with
    | bintreeNil _ => bintreeNil A
    | bintreeCons _ x b1 b2 => bintreeCons A x (espejo A b2) (espejo A b1)
    end.


(* 2.1. *)
Theorem isomorfo_vacio : forall (A : Set) (a : A) (l r : bintree A), 
  ~ isomorfo A (bintreeNil A) (bintreeCons A a l r).
Proof.
  intros A a l r H.
  inversion H.
Qed.

(* 2.2. *)
Theorem isomorfo_subarboles : forall (A : Set) (a1 a2 : A) (l1 r1 l2 r2 : bintree A),
  isomorfo A (bintreeCons A a1 l1 r1) (bintreeCons A a2 l2 r2) -> isomorfo A l1 l2 /\ isomorfo A r1 r2.
Proof.
  intros A a1 a2 l1 r1 l2 r2 H.
  inversion H; split; assumption.
Qed.

Theorem isomorfo_transitiva : forall (A : Set) (ta tb tc : bintree A),
  isomorfo A ta tb /\ isomorfo A tb tc -> isomorfo A ta tc.
Proof.
  intros A ta tb tc [H1 H2].
  revert tc H2.
  induction H1 as [| a b x y z t Hxy IHxy Hzt IHzt]; intros tc H2.
  - assumption.
  - inversion H2.
    subst.
    apply isomorfoS.
    + apply IHxy. assumption.
    + apply IHzt. assumption.
Qed.

Theorem isomorfo_espejo : forall (A : Set) (t1 t2 : bintree A),
  isomorfo A t1 t2 -> isomorfo A (espejo A t1) (espejo A t2).
Proof.
  intros A t1 t2 H.
  induction H;
  simpl.
  - apply isomorfo0.
  - apply isomorfoS; assumption.
Qed.

End Ejercicio2.