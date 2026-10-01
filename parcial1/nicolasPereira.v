(* Nicolas Pereira - 5.139.786-4 *)

Section Problema1.

  Variables Clave Desbloqueado DatosGuardados ErrorSistema : Prop.

  Hypothesis Regla1 : Clave -> Desbloqueado.
  Hypothesis Regla2 : ~ Desbloqueado \/ DatosGuardados.
  Hypothesis Regla3 : ~ (Clave /\ ErrorSistema).


  Theorem t1 : ErrorSistema -> ~ Clave.
  Proof.
    intros es cl.
    absurd (Clave /\ ErrorSistema).
    - assumption.
    - split; assumption.
  Qed.

  Theorem t2 : DatosGuardados \/ ~ Clave.
  Proof.
    elim Regla2.
    - intro ndes.
      right.
      intro c.
      apply ndes.
      apply Regla1.
      assumption.
    - intro dg.
      left.
      assumption.
  Qed.

End Problema1.


Section Problema2.

  Variable D : Set.
  Variable P : forall p : D, Prop.

  Theorem p2 : forall x : D, (P x) -> (exists z: D, (P z)).
  Proof.
    intro x.
    intro px.
    exists x.
    assumption.
  Qed.

End Problema2.


Section Problema3. 

  Variable Proceso Recurso : Set. 
  Variable Asignado : Proceso -> Recurso -> Prop. 
  Variable Bloqueado : Proceso -> Proceso -> Prop.

  Theorem t3 :
    forall p_inicio : Proceso,
    (exists r : Recurso, forall p : Proceso, Asignado p r) ->
    (forall p1 : Proceso, exists p2 : Proceso, Bloqueado p1 p2) ->
    exists x y : Proceso, exists w : Recurso, Bloqueado x y /\ Asignado x w.

  Proof.
    intros pi h h2.
    elim h.
    intros r h3.
    exists pi.
    cut (exists (rw:Recurso) (py:Proceso), Bloqueado pi py /\ Asignado pi rw).
    - intro h4.
      elim h4. intros w h5.
      elim h5. intros y h6.
      exists y. exists w.
      assumption.
    - exists r.
      cut ((exists py:Proceso, Bloqueado pi py) /\ Asignado pi r).
      + intro h4.
        elim h4.
        intros h5 h6.
        elim h5.
        intros px h7.
        exists px.
        split; assumption.
      + split.
        * apply h2.
        * apply h3.
  Qed.

End Problema3.


Section Problema4.

  Variable Bool: Set.
  Variable TRUE FALSE: Bool.
  Variable Not : Bool -> Bool.
  Variable Imp Xor: Bool -> Bool -> Bool.
  Axiom Disc : ~ (FALSE = TRUE).
  Axiom BoolVal : forall b : Bool, b = TRUE \/ b = FALSE.
  Axiom NotTrue : Not TRUE = FALSE.
  Axiom NotFalse : Not FALSE = TRUE.
  Axiom ImpFalse : forall b : Bool, Imp FALSE b = TRUE.
  Axiom ImpTrue : forall b : Bool, Imp TRUE b = b.
  Axiom XorTrue : forall b : Bool, Xor TRUE b = Not b.
  Axiom XorFalse : forall b : Bool, Xor FALSE b = b.

  Lemma l4_1: forall b1 b2: Bool, Imp b1 b2 = FALSE -> b1 = TRUE /\ b2 = FALSE.
  Proof.
    intros b1 b2 h.
    split.
    - cut (b1 = TRUE \/ b1 = FALSE).
      + intro h1. elim h1.
        * intro. assumption.
        * intro h2.
          rewrite -> h2 in h.
          rewrite -> (ImpFalse b2) in h.
          elim Disc.
          symmetry.
          assumption.
      + apply BoolVal.
    - cut (b1 = TRUE \/ b1 = FALSE).
      + intro h1. elim h1.
        * intro h2.
          rewrite <- h.
          symmetry.
          replace b1 with TRUE.
          apply ImpTrue.
        * intro h2.
          rewrite -> h2 in h.
          rewrite -> (ImpFalse b2) in h.
          elim Disc.
          symmetry.
          assumption.
      + apply BoolVal.
  Qed.

  Lemma l4_2: forall b1 b2: Bool, Xor b1 b2 = TRUE -> Imp b1 (Not b2) = TRUE.
  Proof.
    intros b1 b2.
    intro h.
    cut (b1 = TRUE \/ b1 = FALSE).
    - intro h2. elim h2.
      + intro h3.
        rewrite -> h3 in h.
        rewrite -> h3.
        replace (Not b2) with TRUE.
        apply ImpTrue.
        rewrite -> (XorTrue b2) in h.
        symmetry.
        assumption.
      + intro h3.
        rewrite -> h3.
        apply ImpFalse.
    - apply BoolVal.
  Qed.

End Problema4.


Section Problema5.

  Parameter Array : Set -> nat -> Set.
  Parameter emptyA : forall X : Set, Array X 0.
  Parameter addA : forall (X : Set) (n : nat), X -> Array X n -> Array X (S n).

  Parameter ArbNat : forall n : nat, Set.
  Parameter null : ArbNat 0.
  Parameter add : forall n m : nat, nat -> Array (ArbNat n) m -> ArbNat (S n).


  Definition array_vacio_de_arboles_vacios := emptyA (ArbNat 0).
  Definition array_1_arboles_vacios := (addA (ArbNat 0) 0 null array_vacio_de_arboles_vacios).
  Definition array_2_arboles_vacios := (addA (ArbNat 0) 1 null array_1_arboles_vacios).
  Definition array_3_arboles_vacios := (addA (ArbNat 0) 2 null array_2_arboles_vacios).
  Definition ArbNat_3Ario_noVacio := add 0 3 8 array_3_arboles_vacios.

  Check ArbNat_3Ario_noVacio.

  (*
  ArbNat_3Ario_noVacio :


                8
              / | \
             /  |  \
            /   |   \
           /    |    \
          /     |     \
      (null)  (null)  (null)
  *)

End Problema5.