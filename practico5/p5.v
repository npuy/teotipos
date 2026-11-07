(* Nicolas Pereira - 5.139.786-4 *)

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

Section Ejercicio3.
(* Ejercicio 5.3. Se quiere definir conjuntos en Coq como una restricción de listas.  
1. Defina, a partir de las siguientes declaraciones, la relación inductiva unaria isSet que contiene a las 
listas sin elementos repetidos.  *)
Variable A : Set.  

Parameter equal : A -> A -> bool. 
Axiom equal1 : forall x y : A, equal x y = true -> x = y. 
Axiom equal2 : forall x : A, equal x x <> false.  

Inductive List : Set :=   
| nullL : List   
| consL : A -> List -> List.  

Inductive MemL (a : A) : List -> Prop :=   
| hereL : forall x : List, MemL a (consL a x)   
| thereL : forall x : List, MemL a x -> forall b : A, MemL a (consL b x).  

Inductive isSet : List -> Prop := 
| nullSet : isSet nullL
| consSet : forall (a : A) (l : List), isSet l -> ~ (MemL a l) -> isSet (consL a l).

(* 2. Defina una función recursiva deleteAll que dado un elemento y una lista, elimine todas las 
ocurrencias del elemento de la lista.  *)
Fixpoint deleteAll (a : A) (l : List) : List :=
  match l with
  | nullL => nullL
  | consL x lr =>
    if equal a x
    then deleteAll a lr
    else consL x (deleteAll a lr)
  end.


(* 3. Pruebe la siguiente propiedad: *)
Lemma DeleteAllNotMember : forall (l : List) (x : A),  
  ~ MemL x (deleteAll x l). 
Proof.
  intros l x H.
  induction l.
  - inversion H.
  - simpl in H.
    destruct (equal x a) eqn:E.
    + contradiction.
    + inversion H.
      * subst. 
        apply (equal2 a).
        assumption.
      * contradiction.
Qed.

(* 4. Defina una función recursiva delete que dado un elemento y una lista, elimine la primera ocurrencia 
del elemento de la lista.  *)
Fixpoint delete (a : A) (l : List) : List :=
  match l with
  | nullL => nullL
  | consL x lr =>
    if equal a x
    then lr
    else consL x (delete a lr)
  end.


(* 5. Pruebe la siguiente propiedad inherente a los conjuntos:   *)
Lemma DeleteNotMember : forall (l : List) (x : A), isSet l ->   
  ~ MemL x (delete x l).  
Proof.
  intros l x H H1.
  induction l.
  - simpl in H1.
    inversion H1.
  - simpl in H1.
    destruct (equal x a) eqn:E.
    + inversion H. 
      apply equal1 in E.
      subst.
      contradiction.
    + inversion H.
      inversion H1; subst.
      * apply (equal2 a). assumption.
      * apply IHl; assumption.
Qed.

End Ejercicio3.

Section Ejercicio4.
(* Ejercicio 5.4. Considere la siguiente definición de árboles binarios de elementos de un tipo genérico:  *)
Variable A : Set.   
Inductive AB: Set :=     
  | null : AB    
  | cons: A -> AB-> AB -> AB. 

(* a)  Defina inductivamente la relación Pertenece de pertenencia de un elemento a un árbol binario de 
tipo AB.  *)
Inductive Pertenece: A -> AB -> Prop :=
  | hereAB : forall (a : A) (l r : AB), Pertenece a (cons a l r)
  | thereLeftAB : forall (a b : A) (l r : AB), Pertenece a l -> Pertenece a (cons b l r)
  | thereRigthAB : forall (a b : A) (l r : AB), Pertenece a r -> Pertenece a (cons b l r).

(* b)  Defina una función recursiva Borrar que dado un árbol binario ab de tipo AB y un elemento x de 
tipo A retorne el árbol sin aquellos subárboles de ab que tienen a x como raíz. 

Asuma el siguiente parámetro para la igualdad de elementos de tipo A:  *)
Parameter eqGen: A->A->bool. 

Fixpoint Borrar (a : A) (t : AB) : AB :=
  match t with
  | null => null
  | cons x l r =>
    if eqGen a x
    then null
    else cons x (Borrar a l) (Borrar a r)
  end.

(* c)  Pruebe el lema:  *)
(* Asuma la siguiente propiedad referente a la igualdad de elementos de tipos A:  *)
Axiom eqGen1: forall (x:A), ~(eqGen x x)=false.  

Lemma BorrarNoPertenece: forall (x:AB) (a:A), ~(Pertenece a (Borrar a x)).  
Proof.
  intros t a H.
  induction t as [| x l IHl r IHr].
  - inversion H.
  - simpl in H.
    destruct (eqGen a x) eqn:E.
    + inversion H.
    + inversion H; subst.
      * apply eqGen1 in E. assumption.
      * apply IHl. assumption.
      * apply IHr. assumption.
Qed.

(* d) Defina inductivamente la relación SinRepetidos que contiene a los árboles binarios sin elementos 
repetidos. El árbol vacío pertenece a la relación.   *)
Inductive SinRepetidos : AB -> Prop :=
  | nullSR : SinRepetidos null
  | consSR : forall (a : A) (l r : AB), 
    SinRepetidos l -> SinRepetidos r -> 
    ~(Pertenece a l) -> ~(Pertenece a r) -> 
    (forall (b : A), Pertenece b l -> ~ Pertenece b r) ->
    SinRepetidos (cons a l r).

End Ejercicio4.

Section Ejercicio5.
(* Ejercicio 5.5.  Considere la siguiente gramática para expresiones booleanas: 
Var  : =   0  |  1  |  2 | ... 
bool   : =   true  | false  
BE  : =   Var   
  | bool   
  | (  BE  /\  BE  )   
  | ( ~  BE )  
1. Defina en Coq los tipos Var como el conjunto de naturales y BoolExpr para representar 
el lenguaje BE.   *)
Definition Var := nat.

Inductive BoolExpr : Set :=
  | bvar : Var -> BoolExpr
  | bbool : bool -> BoolExpr
  | band : BoolExpr -> BoolExpr -> BoolExpr
  | bnot : BoolExpr -> BoolExpr.

(* 2. La memoria es una función que asocia un valor booleano a cada variable y se dispone de 
una función lookup que dada una memoria y una variable, devuelve el valor de la 
variable en la memoria; lookup: Memoria -> Var -> Valor. La notación (e, )  w se lee 
“la expresión booleana e se evalúa al valor booleano w en la memoria ”.  
Definimos la relación de evaluación de expresiones booleanas en un estado de la 
memoria , donde el conjunto de valores es bool, de acuerdo a las siguientes reglas:   
Regla evar: (v, )  (lookup  v)   
Regla eboolt: (true, )  true   
Regla eboolf: (false, )  false  
Regla eandl: Si (e1,)  false entonces ((e1e2),)  false   
Regla eandr: Si (e2,)  false entonces ((e1e2),)  false   
Regla eandrl: Si (e1,)  true y (e2,)  true entonces ((e1e2),)  true  
Regla enott: Si (e,)  true entonces (e,  false   
Regla enotf: Si (e,)  false entonces (e,  true 
Defina en Coq los tipos Valor, Memoria y la relación BEval definida por las reglas 
anteriores.   *)
Definition Valor := bool.

Definition Memoria := Var -> Valor.
Definition lookup (m:Memoria) (v:Var) : Valor := m v.

Inductive BEval : BoolExpr -> Memoria -> Valor -> Prop :=
  | evar : forall (v : Var) (m : Memoria), BEval (bvar v) m (lookup m v)
  | eboolt : forall (m : Memoria), BEval (bbool true) m true
  | eboolf : forall (m : Memoria), BEval (bbool false) m false
  | eandl : forall (e1 e2 : BoolExpr) (m : Memoria), 
      BEval e1 m false -> BEval (band e1 e2) m false
  | eandr : forall (e1 e2 : BoolExpr) (m : Memoria), 
      BEval e2 m false -> BEval (band e1 e2) m false
  | eandrl : forall (e1 e2 : BoolExpr) (m : Memoria), 
      BEval e1 m true -> BEval e2 m true -> BEval (band e1 e2) m true
  | enott : forall (e : BoolExpr) (m : Memoria), 
      BEval e m true -> BEval (bnot e) m false
  | enotf : forall (e : BoolExpr) (m : Memoria), 
      BEval e m false -> BEval (bnot e) m true.

(* 3. Demuestre en Coq las siguientes propiedades:  
a. Para toda memoria  la expresión true evaluada en la memoria  nunca da el valor false.  
b. Si (e1,   true y si (e2,   w entonces (e1e2, )  w cualesquiera sean , e1, e2 y w.  
c. Si (e,   w1 y (e,   w2 entonces w1 = w2, cualesquiera sean w1 y w2.  
d. Si (e1,   false entonces no se da que ((e1e2),  true, cualesquiera sean e1 y e2.   *)

Theorem teo_a : forall (m : Memoria), ~ BEval (bbool true) m false.
Proof.
  intros m H.
  inversion H.
Qed.

Theorem teo_b : forall (m : Memoria) (e1 e2 : BoolExpr) (w : Valor),
  BEval e1 m true /\ BEval e2 m w -> BEval (band e1 e2) m w.
Proof.
  intros m e1 e2 w H.
  elim H.
  intros H1 H2.
  induction w.
  - apply eandrl; assumption.
  - apply eandr. assumption.
Qed.

Theorem teo_c : forall (m : Memoria) (e : BoolExpr) (w1 w2 : Valor),
  BEval e m w1 /\ BEval e m w2 -> w1 = w2.
Proof.
  intros m e w1 w2 [H1 H2].
  revert w2 H2.
  induction H1; intros w2 H2; inversion H2; subst; try reflexivity.
  - apply IHBEval. assumption.
  - apply IHBEval. assumption.
  - apply IHBEval1. assumption.
  - apply IHBEval2. assumption.
  - symmetry. apply IHBEval. assumption.
  - symmetry. apply IHBEval. assumption.
  (* induction H1; intros w2 H2; inversion H2.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - subst. apply IHBEval. assumption.
  - reflexivity.
  - reflexivity.
  - subst. apply IHBEval. assumption.
  - subst. apply IHBEval1. assumption.
  - subst. apply IHBEval2. assumption.
  - reflexivity.
  - reflexivity.
  - subst. symmetry. apply IHBEval. assumption.
  - subst. symmetry. apply IHBEval. assumption.
  - reflexivity. *)
Qed.

Theorem teo_d : forall (m : Memoria) (e1 e2 : BoolExpr),
  BEval e1 m false -> BEval (bnot (band e1 e2)) m true.
Proof.
  intros m e1 e2 H.
  apply enotf.
  apply eandl.
  assumption.
Qed.

(* 4. Escriba en Coq una función beval:Memoria->BoolExpr->Valor que evalúe las 
expresiones booleanas por valor (o sea que evalúe todas las subexpresiones de una 
expresión).   *)

Fixpoint beval (m:Memoria) (e:BoolExpr) : Valor :=
  match e with
  | bvar var => lookup m var
  | bbool b => b
  | band a b =>
    if beval m a
    then 
      if beval m b
      then true
      else false
    else 
      if beval m b
      then false
      else false
  | bnot a =>
    if beval m a
    then false
    else true
  end.

(* 5. Demuestre que la función definida en la parte anterior es una estrategia correcta de 
evaluación con respecto a la relación . Es decir que (e,   (beval  e). *)

Theorem teo_5_5 : forall (m : Memoria) (e : BoolExpr), BEval e m (beval m e).
Proof.
  intros m e.
  induction e; simpl.
  - apply evar.
  - destruct b.
    + apply eboolt.
    + apply eboolf.
  - destruct (beval m e1);
    destruct (beval m e2).
    + apply eandrl; assumption.
    + apply eandr; assumption.
    + apply eandl; assumption.
    + apply eandl; assumption.
  - destruct (beval m e).
    + apply enott; assumption.
    + apply enotf; assumption.
Qed.

End Ejercicio5.