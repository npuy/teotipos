(* Datos del o de los estudiantes *)
(* Nicolas Pereira - 5.139.786-4 *)

Section Ejercicio1.

Variable U  : Set.
Variable A B: U -> Prop.
Variable P Q: Prop.
Variable R S: U -> U -> Prop.

Theorem e11 : (forall x:U, A(x)) -> forall y:U, A(y).
Proof.
    intro h.
    apply h.
Qed.

Theorem e12 : (forall x y:U, (R x y)) -> forall x y:U, (R y x).
Proof.
    intro h.
    intros hx hy.
    apply h.
Qed.


Theorem e13 : (forall x: U, ((A x)->(B x)))
                    -> (forall y:U, (A y))
                        -> (forall z:U, (B z)).
Proof.
    intro h.
    intro h2.
    intro hz.
    apply h.
    apply h2.
Qed.


End Ejercicio1.


Section Ejercicio2.

Variable U  : Set.
Variable A B: U -> Prop.
Variable P Q: Prop.
Variable R S: U -> U -> Prop.


Theorem e21 : (forall x:U, ((A x)-> ~(forall x:U, ~ (A x)))).
Proof.
    intro x1.
    intro ax1.
    intro h.
    absurd (A x1).
    - apply h.
    - assumption.
Qed.

Theorem e22 : (forall x y:U, ((R x y)))-> (forall x:U, (R x x)).
Proof.
    intro h.
    intro x.
    apply h.
Qed.

Theorem e23 : (forall x:U, ((P -> (A x))))
                        -> (P -> (forall x: U, (A x))).
Proof.
    intro h.
    intro hp.
    intro x.
    apply h.
    assumption.
Qed.


Theorem e24 : (forall x:U, ((A x) /\ (B x)))
                        -> (forall x:U, (A x))
                          -> (forall x:U, (B x)).
Proof.
    intro h.
    intro h2.
    intro x.
    apply h.
Qed.


Theorem e25 : (forall x:U, (A x)) \/ (forall x:U, (B x)) -> 
                      forall x:U, ~(~(A x) /\ ~(B x)).
Proof.
    intro h.
    intro x.
    intro h2.
    elim h.
    - intro ha.
      absurd (A x).
      + elim h2.
        intro hna.
        intro hnb.
        assumption.
      + apply ha.
    - intro hb.
      absurd (B x).
      + elim h2.
        intro hna.
        intro hnb.
        assumption.
      + apply hb.
Qed.


End Ejercicio2.


Section Ejercicio3.

Variable U   : Set.
Variable A B : U -> Prop.
Variable P Q : Prop.
Variable R S : U -> U -> Prop.

Definition H1 := forall x:U, (R x x).
Definition H2 := forall x y z:U, (R x y) /\ (R x z) -> (R y z).

Theorem e231: H1 /\ H2 -> (forall x : U, (R x x)) /\ (forall x y : U, (R x y) -> (R y x)) /\ (forall x y z : U, (R x y) /\ (R y z) -> (R x z)).
Proof.
    intro h.
    elim h.
    intro h1.
    intro h2.
    split.
    - assumption.
    - split.
      + intros x y rxy.
        apply (h2 x y).
        split.
        * assumption.
        * apply h1.
      + intros x y z hand.
        elim hand.
        intros hrxy hryz.
        cut (forall x y : U, (R x y) -> (R y x)).
        * intro hsim.
          cut (R y x).
          -- intro hryx.
             apply (h2 y x z).
             split.
             ++ assumption.
             ++ assumption.
          -- apply (hsim).
             assumption.
        * intros x0 y0 hrx0y0.
          apply (h2 x0 y0).
          split.
          -- assumption.
          -- apply h1.
Qed.

Definition Irreflexiva := forall x : U, ~ (R x x).
Definition Asimetrica := forall x y : U, (R x y) -> ~ (R y x).
 
Lemma e232 : Asimetrica -> Irreflexiva.
Proof.
    intro asim.
    intros x rxx.
    absurd (R x x).
    - apply asim.
      assumption.
    - assumption.
Qed.

End Ejercicio3.


Section Ejercicio4.

Variable U : Set.
Variable A B : U->Prop.
Variable R : U->U->Prop.

Theorem e41: (exists x:U, exists y:U, (R x y)) -> 
                exists y:U, exists x:U, (R x y).
Proof.
    intro h.
    elim h.
    intro x.
    intro h2.
    elim h2.
    intro y.
    intro rxy.
    exists y.
    exists x.
    assumption.
Qed.

Theorem e42: (forall x:U, A(x)) -> 
                ~ exists x:U, ~ A(x).
Proof.
    intro h.
    intro h2.
    elim h2.
    intro x.
    intro nax.
    absurd (A x).
    - assumption.
    - apply h.
Qed.

Theorem e43: (exists x:U, ~(A x)) -> 
                ~(forall x:U, (A x)).
Proof.
    intro h.
    intro h2.
    elim h.
    intro x.
    intro nax.
    absurd (A x).
    - assumption.
    - apply h2.
Qed.

Theorem e44: (forall x:U, ((A x) /\ (B x)))
                -> (forall x:U, (A x)) /\ (forall x:U, (B x)).
Proof.
    intro h.
    split.
    - apply h.
    - apply h.
Qed.

Theorem e45: (exists x:U, (A x \/ B x))->
                (exists x:U, A x) \/ (exists x:U, B x).
Proof.
    intro h.
    elim h.
    intro x.
    intro aob.
    elim aob.
    - intro ax.
      left.
      exists x.
      assumption.
    - intro bx.
      right.
      exists x.
      assumption.
Qed.

Theorem e46: (forall x:U, A x) \/ (forall y:U, B y) 
                -> forall z:U, A z \/ B z.
Proof.
    intro h.
    intro x.
    elim h.
    - intro h1.
      left.
      apply h1.
    - intro h1.
      right.
      apply h1.
Qed.



End Ejercicio4.


Section Ejercicio5.

Variable nat      : Set.
Variable S        : nat -> nat.
Variable a b c    : nat.
Variable odd even : nat -> Prop.
Variable P Q      : nat -> Prop.
Variable f        : nat -> nat.

Theorem e51: forall x:nat, exists y:nat, (P(x)->P(y)).
Proof.
    intro x.
    exists x.
    intro px.
    assumption.
Qed.

Theorem e52: exists x:nat, (P x)
                            -> (forall y:nat, (P y)->(Q y))
                               -> (exists z:nat, (Q z)).
Proof.
    exists a.
    intro pa.
    intro h.
    exists a.
    apply h.
    assumption.
Qed.


Theorem e53: even(a) -> (forall x:nat, (even(x)->odd (S(x)))) -> exists y: nat, odd(y).
Proof.
    intro h.
    intro h1.
    exists (S a).
    apply h1.
    assumption.
Qed.


Theorem e54: (forall x:nat, P(x) /\ odd(x) ->even(f(x)))
                            -> (forall x:nat, even(x)->odd(S(x)))
                            -> even(a)
                            -> P(S(a))
                            -> exists z:nat, even(f(z)).
Proof.
    intro h.
    intro h2.
    intro ea.
    intro psa.
    exists (S a).
    apply h.
    split.
    - assumption.
    - apply h2.
      assumption.
Qed.

End Ejercicio5.


Section Ejercicio6.

Variable nat : Set.
Variable S   : nat -> nat.
Variable le  : nat -> nat -> Prop.
Variable f   : nat -> nat.
Variable P   : nat -> Prop.

Axiom le_n: forall n:nat, (le n n).
Axiom le_S: forall n m:nat, (le n m) -> (le n (S m)).
Axiom monoticity: forall n m:nat, (le n m) -> (le (f n) (f m)).


Lemma le_x_Sx: forall x:nat, (le x (S x)).
Proof.
    intro x.
    apply le_S.
    apply le_n.
Qed.

Lemma le_x_SSx: forall x:nat, (le x (S (S x))).
Proof.
    intro x.
    apply le_S.
    apply le_x_Sx.
Qed.

Theorem T1: forall a:nat, exists b:nat, (le (f a) b).
Proof.
    intro a.
    exists (S (f a)).
    apply le_S.
    apply le_n.
Qed.

Theorem T1_2: forall a:nat, exists b:nat, (le (f a) b).
Proof.
    intro a.
    exists (S (S (S (S (S (f a)))))).
    repeat apply le_S.
    apply le_n.
Qed.

Theorem T1_3: forall a:nat, exists b:nat, (le (f a) b).
Proof.
    intro a.
    exists (S (S (S (S (f a))))).
    do 4 apply le_S.
    apply le_n.
Qed.

End Ejercicio6.



Section Ejercicio7.

Variable U   : Set.
Variable A B : U -> Prop.

Theorem e71: (forall x:U, ((A x) /\ (B x)))
                       -> (forall x:U, (A x)) /\ (forall x:U, (B x)).
Proof.
    intro h; split; apply h.
Qed.

Theorem e72: (exists x:U, (A x \/ B x))->(exists x:U, A x )\/(exists x:U, B x).
Proof.
    intro h; elim h; intros x aob; elim aob; intro hh; [left | right]; exists x; assumption.
Qed.

Theorem e73: (forall x:U, A x) \/ (forall y:U, B y) -> forall z:U, A z \/ B z.
Proof.
    intros h x; elim h; intro hh; [left | right]; apply hh.
Qed.

End Ejercicio7.


Section Ejercicio8.

Variables U : Set.
Variables T V : U -> Prop.
Variables R : U -> U -> Prop.

Theorem e81: (exists y : U, forall x : U, R x y) -> forall x : U, exists y : U, R x y.
Proof.
    intro h.
    intro x.
    elim h.
    intro y.
    intro h2.
    exists y.
    apply h2.
Qed.

Theorem e82:
  (exists x:U, True) /\ (forall x:U, (T x) \/ (V x))
    -> (exists z:U, (T z)) \/ (exists w:U, (V w)).
Proof.
    intro h.
    elim h.
    intro h1.
    intro h2.
    elim h1.
    intro x.
    intro t.
    cut (T x \/ V x).
    - intro h3; elim h3; intro hx; [left | right]; exists x; assumption.
    - apply h2.
Qed.

(* 
Parte 8.3. La proposición (exists x:U, True) ...
entiendo que es necesaria porque en caso de no estar 
podemos decir que U es el conjunto vacio
y T y V son las funciones constantes True
y en ese caso:
*)
Theorem e83_falso :
  ~ (forall (U:Set) (T V : U -> Prop),
       (forall x:U, (T x) \/ (V x)) -> (exists z:U, (T z)) \/ (exists w:U, (V w))).
Proof.
  intro H.
  elim (H Empty_set (fun _ => True) (fun _ => True)).
  - intro e. elim e. intro x. elim x.
  - intro e. elim e. intro x. elim x.
  - intro x. elim x.
Qed.

End Ejercicio8.


Require Import Classical.

Section Ejercicio9.
Variables U : Set.
Variables A : U -> Prop.

Lemma not_ex_not_forall: (~exists x :U, ~A x) -> (forall x:U, A x).
Proof.
    intros h x.
    elim (classic (A x)).
    - intro a; assumption.
    - intro na.
      elim h.
      exists x.
      assumption.
Qed.

Lemma not_forall_ex_not: (~forall x :U, A x) -> (exists x:U,  ~A x).
Proof.
    intro h.
    apply NNPP.
    intro hne.
    absurd (forall x:U, A x).
    - assumption.
    - apply not_ex_not_forall.
      assumption.
Qed.

End Ejercicio9.


Section Ejercicio10_11.

Variable nat : Set.
Variable  O  : nat.
Variable  S  : nat -> nat.

Axiom disc   : forall n:nat, ~O=(S n).
Axiom inj    : forall n m:nat, (S n)=(S m) -> n=m.
Axiom allNat : forall n: nat, n = O \/ exists m: nat, S m = n.

Variable sum prod : nat->nat->nat.

Axiom sum0   : forall n :nat, (sum n O)=n.
Axiom sumS   : forall n m :nat, (sum n (S m))=(S (sum n m)).
Axiom prod0  : forall n :nat, (prod n O)=O.
Axiom prodS  : forall n m :nat, (prod n (S m))=(sum n (prod n m)).

Lemma L10_1: (sum (S O) (S O)) = (S (S O)).
Proof.
    replace (sum (S O) (S O)) with (S (sum (S O) O)).
    - replace (sum (S O) O) with (S O).
      + reflexivity.
      + symmetry; apply sum0.
    - symmetry. apply sumS.
Qed.

Lemma L10_2: forall n :nat, ~(O=n /\ (exists m :nat, n = (S m))).
Proof.
    intros n h.
    elim h.
    intros h1 h2.
    elim h2.
    intros m h3.
    absurd (O = (S m)).
    - apply disc.
    - transitivity n; assumption.
Qed.

Lemma prod_neutro: forall n :nat, (prod n (S O)) = n.
Proof.
    intro n.
    transitivity (sum n (prod n O)).
    - apply prodS.
    - replace (prod n O) with O.
      + apply sum0.
      + symmetry; apply prod0.
Qed.

Lemma diff: forall n:nat, ~(S (S n))=(S O).
Proof.
    intros n h.
    absurd ((O = (S n))).
    - apply disc.
    - symmetry; apply inj; assumption.
Qed.

Lemma L10_3: forall n: nat, exists m: nat, prod n (S m) = sum n n. 
Proof.
    intro n.
    exists (S O).
    transitivity (sum n (prod n (S O))).
    - apply prodS.
    - replace (prod n (S O)) with n.
      + reflexivity.
      + symmetry; apply prod_neutro.
Qed.

Lemma L10_4: forall m n: nat, n <> O -> sum m n <> O.  
Proof.
    intros m n hn hsum.
    elim (allNat n).
    - assumption.
    - intro h.
      elim h.
      intros p hp.
      absurd (O = (S (sum m p))).
      + apply disc.
      + rewrite <- hsum.
        rewrite <- hp.
        apply sumS.
Qed.

Lemma L10_5: forall m n: nat, sum m n = O -> m = O /\ n = O.  
Proof.
    intros m n h.
    elim (allNat n).
    - intro hn. 
      rewrite -> hn in h.
      rewrite -> sum0 in h.
      split; assumption.
    - intro hh.
      elim hh.
      intros p hp.
      absurd (O = (S (sum m p))).
      + apply disc.
      + rewrite <- h.
        rewrite <- hp.
        apply sumS.

    (* 
    Primer intento
    
    intros m n h.
    split.
    - elim (allNat m).
      + intro hh; assumption.
      + intro hh.
        elim hh.
        intro p.
        intro hp.
        absurd (n = O).
        * intro hn.
          rewrite <- hn in h.
          absurd ((S p) = O).
          -- symmetry; apply disc.
          -- rewrite <- hp in h.
             rewrite -> hn in h.
             transitivity (sum (S p) O).
             ++ symmetry. apply sum0.
             ++ assumption.
        * elim (allNat n).
          -- intro no; assumption.
          -- intro h2.
             elim h2.
             intro q.
             intro hq.
             absurd (O = (S (sum m q))).
             ++ apply disc.
             ++ rewrite <- h.
                rewrite <- hq.
                apply sumS.
    - elim (allNat n).
      + intro no; assumption.
      + intro h2.
        elim h2.
        intro q.
        intro hq.
        absurd (O = (S (sum m q))).
        * apply disc.
        * rewrite <- h.
          rewrite <- hq.
          apply sumS. *)
Qed.

Lemma L10_6: forall m n: nat, prod m n = O -> m = O \/ n = O.
Proof.
    intros m n h.
    elim (allNat n).
    - intro hn.
      right; assumption.
    - intro h2.
      elim h2.
      intros q hq.
      left.
      rewrite <- hq in h.
      rewrite prodS in h.
      elim (L10_5 m (prod m q) h).
      intros hm hpq; assumption.
Qed.

Variable le : nat->nat->Prop.
Axiom leinv: forall n m:nat, (le n m) -> n=O \/
      (exists p:nat, (exists q:nat, n=(S p) /\ m=(S q) /\ (le p q))).

Lemma notle_s_o: forall n:nat, ~(le (S n) O).
Proof.
    intro p.
    intro h.
    cut ((S p) = O \/ (exists x y: nat, ((S p) = (S x) /\ O = (S y) /\ (le x y)))).
    - intro h1.
      elim h1.
      + intro s.
        cut (O = (S p)).
        * apply disc.
        * symmetry.
          assumption.
      + intro h2.
        elim h2.
        intro x.
        intro h3.
        elim h3.
        intros y h4.
        elim h4.
        intros h5 h6.
        elim h6.
        intros h7 h8.
        cut (O = (S y)).
        * apply disc.
        * assumption.
    - apply (leinv (S p) O).
      assumption.
Qed.

End Ejercicio10_11.