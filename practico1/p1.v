(* Práctico 1 *)

(* Datos del estudiante o de los estudiantes *)
(* Nicolas Pereira - 5.139.786-4 *)

Section P1.
Variables A B C:Prop.

(* Ej 1.1 *)
Theorem e11: A->A.
Proof.
    intro H.
    assumption.
Qed.

(* Ej 1.2 *)
Theorem e12: A->B->A.
Proof.
    intro Ha.
    intro Hb.
    assumption.
Qed.

(* Ej 1.3 *)
Theorem e13: (A->(B->C))->(A->B)->(A->C).
Proof.
    intro Habc.
    intro Hab.
    intro Ha.
    apply Habc.
    - assumption.
    - apply Hab.
      assumption.
Qed.

(*Ej 2.1 *)
Theorem e21: (A->B)->(B->C)->A->C.
Proof.
    intro Hab.
    intro Hbc.
    intro Ha.
    apply Hbc.
    apply Hab.
    assumption.
Qed.

(*Ej 2.2 *)
Theorem e22: (A->B->C)->B->A->C.
Proof.
    intro Habc.
    intro Hb.
    intro Ha.
    apply Habc.
    - assumption.
    - assumption.
Qed.

(*Ej 3.1 *)
Theorem e31_1: A->A->A.
Proof.
    intro Ha.
    intro Haa.
    assumption.
Qed.

Theorem e31_2: A->A->A.
Proof.
    intro Ha.
    exact e11.
Qed.

(* Ej 3.2 *)
Theorem e32_1: (A->B->C)->A->(A->C)->B->C.
Proof.
    intro Habc.
    intro Ha.
    intro Hac.
    intro Hb.
    apply Hac.
    assumption.
Qed.

Theorem e32_2: (A->B->C)->A->(A->C)->B->C.
Proof.
    intro Habc.
    intro Ha.
    intro Hac.
    intro Hb.
    apply Habc.
    - assumption.
    - assumption.
Qed.

(* Ej 4.1 *)
Theorem e41: A -> ~~A.
Proof.
    intro Ha.
    unfold not.
    intro Han.
    apply Han.
    assumption.
Qed.

(* Ej 4.2 *)
Theorem e42: A -> B -> (A /\ B).
Proof.
    intro ha.
    intro hb.
    split.
    - assumption.
    - assumption.
Qed.

(* Ej 4.3 *)
Theorem e43: (A->B->C) -> (A/\B->C).
Proof.
    intro habc.
    intro hab.
    elim hab.
    assumption.
Qed.

(* Ej 4.4 *)
Theorem e44: A->(A\/B).
Proof.
    intro ha.
    left.
    assumption.
Qed.

(* Ej 4.5 *)
Theorem e45: B->(A\/B).
Proof.
    intro ha.
    right.
    assumption.
Qed.

(* Ej 4.6 *)
Theorem e46: (A \/ B) -> (B \/ A).
Proof.
    intro hab.
    elim hab.
    - right.
      assumption.
    - left.
      assumption.
Qed.

(* Ej 4.7 *)
Theorem e47: (A->C)->(B->C)->A\/B->C.
Proof.
    intro hac.
    intro hbc.
    intro hab.
    elim hab.
    - assumption.
    - assumption.
Qed.

(* Ej 4.8 *)
Theorem e48: False->A.
Proof.
    intro hf.
    elim hf.
Qed.

(* Ej 5.1 *)
Theorem e51: (A->B)-> ~B-> ~A.
Proof.
    intro hab.
    unfold not.
    intro hbf.
    intro ha.
    apply hbf.
    apply hab.
    assumption.
Qed.

(* Ej 5.2 *)
Theorem e52: ~(A/\~A).
Proof.
    unfold not.
    intro h.
    elim h.
    intro ha.
    intro haf.
    apply haf.
    assumption.
Qed.

(* Ej 5.3 *)
Theorem e53: (A->B)-> ~(A/\~B).
Proof.
    intro hab.
    unfold not.
    intro h.
    elim h.
    intro ha.
    intro hbf.
    elim hbf.
    apply hab.
    assumption.
Qed.

(* Ej 5.4 *)
Theorem e54: (A/\B)->~(A->~B).
Proof.
    intro hab.
    unfold not.
    intro habf.
    elim hab.
    assumption.
Qed.

(* Ej 5.5 *)
Theorem e55: (~A /\ ~~A) -> False.
Proof.
    unfold not.
    intro h.
    elim h.
    intro h1.
    intro h2.
    apply h2.
    assumption.
Qed.

(* Ej 6.1 *)
Theorem e61: (A\/B) -> ~(~A/\~B).
Proof.
    unfold not.
    intro h.
    intro h2.
    elim h2.
    intro h3.
    intro h4.
    elim h.
    - assumption.
    - assumption.
Qed.

(* Ej 6.2 *)
Theorem e62: A\/B <-> B\/A.
Proof.
    unfold iff.
    split.
    - exact e46. 
    - intro hba.
      elim hba.
        right.
        assumption.
        left.
        assumption.
Qed.

(* Ej 6.3 *)
Theorem e63: A\/B -> ((A->B)->B).
Proof.
    intro haOb.
    intro haTb.
    elim haOb.
    - assumption.
    - intro hb. 
      assumption.
Qed.

End P1.


Require Import Classical.
Check classic.

Section Logica_Clasica.
Variables A B C: Prop.

(* Ej 7.1 *)
Theorem e71: A \/ ~A -> ~~A->A.
Proof.
    intro h.
    intro hnna.
    elim h.
    - intro ha.
      assumption.
    - intro hna.
      absurd (~A).
      + assumption.
      + assumption.
Qed.

(* Ej 7.2 *)
Theorem e72: A\/~A -> ((A->B) \/ (B->A)).
Proof.
    intro h.
    elim h.
    - intro ha.
      right.
      intro hb.
      assumption.
    - intro hna.
      left.
      intro ha.
      absurd (A).
      + assumption.
      + assumption.
Qed.

(* Ej 7.3 *)
Theorem e73: (A \/ ~A) -> ~(A /\ B) -> ~A \/ ~B.
Proof.
    intro h.
    intro h2.
    elim h.
    - intro ha.
      right.
      unfold not.
      intro hb.
      absurd (A /\ B).
      + assumption.
      + split.
        * assumption. 
        * assumption. 
    - intro hna.
      left. 
      assumption.
Qed.

(* Ej 8.1 *)
Theorem e81: forall A:Prop, ~~A->A.
Proof.
    unfold not.
    intro A0.
    intro h.
    elim (classic A0).
    - intro ha.
      assumption.
    - intro hna.
      absurd (~A0).
      + assumption.
      + assumption.
Qed.

(* Ej 8.2 *)
Theorem e82: forall A B:Prop, (A->B)\/(B ->A).
Proof.
    intro A0.
    intro B0.
    elim (classic A0).
    - intro ha.
      right.
      intro hb.
      assumption.
    - intro hna.
      left.
      intro ha.
      absurd (A0).
      + assumption.
      + assumption.
Qed.

(* Ej 8.3 *)
Theorem e83: forall A B:Prop, ~(A/\B)-> ~A \/ ~B.
Proof.
    intro A0.
    intro B0.
    intro h2.
    elim (classic A0).
    - intro ha.
      right.
      unfold not.
      intro hb.
      absurd (A0 /\ B0).
      + assumption.
      + split.
        * assumption.
        * assumption.
    - intro hna.
      left. 
      assumption.
Qed.

End Logica_Clasica.


Section Traducciones.

(* Ej 9 *)
(* Definiciones *)
Variable NM RED CONS UTIL : Prop.

Hypothesis Hip1 : ~ NM \/ ~ RED.
Hypothesis Hip2 : CONS \/ ~ UTIL.

Theorem ej9 : (NM /\ UTIL) -> (CONS /\ ~ RED).
Proof.
    intro h1.
    elim h1.
    intro hNM.
    intro hUTIL.
    split.
    - elim Hip2.
      intro hCONS.
      assumption.
      intro hnUTIL.
      elim hnUTIL.
      assumption.
    - elim Hip1.
      intro hnNM.
      elim hnNM.
      assumption.
      intro hnRED.
      assumption.
Qed.


(* Ej 10 y 11 *)
Variables A B C:Prop.
(* Formalizaciones a cargo de los estudiantes *)
Theorem e10e12: A->B->A.
Proof.
    tauto.
Qed.
Theorem e10e13: (A->(B->C))->(A->B)->(A->C).
Proof.
    tauto.
Qed.
Theorem e10e71: A \/ ~A -> ~~A->A.
Proof.
    tauto.
Qed.

(* Ejercicio 1.11.  Considere el siguiente problema: Un club escocés tiene las siguientes reglas para 
aceptar a sus miembros:  
Regla 1: Todo no escocés debe usar medias rojas.  
Regla 2: Todo miembro usa kilt o no usa medias rojas.  
Regla 3: Los miembros casados no salen los domingos.  
Regla 4: Un miembro sale los domingos si y sólo si es escocés.  
Regla 5: Todo miembro que usa kilt es escocés y es casado.  
Regla 6: Todo miembro escocés usa kilt.  
1. Formalice el problema en Coq.  
2. Observe que con las reglas previas nadie puede ser aceptado. Para justificar formalmente 
esto pruebe que las reglas son contradictorias: 
i) sin usar tácticas automáticas.
ii)  usando la táctica tauto.  *)
Variable EsMiembro:Prop.
Variable EsEscoces:Prop.
Variable UsaMediasRojas:Prop.
Variable UsaKilt:Prop.
Variable SaleDomingos:Prop.
Variable EsCasado:Prop.

Hypothesis Regla1 : EsMiembro -> (~ EsEscoces -> UsaMediasRojas).
Hypothesis Regla2 : EsMiembro -> (UsaKilt \/ ~ UsaMediasRojas).
Hypothesis Regla3 : EsMiembro -> (EsCasado -> ~SaleDomingos).
Hypothesis Regla4 : EsMiembro -> (SaleDomingos <-> EsEscoces).
Hypothesis Regla5 : EsMiembro -> (UsaKilt -> (EsEscoces /\ EsCasado)).
Hypothesis Regla6 : EsMiembro -> (EsEscoces -> UsaKilt).

Theorem ej11i: ~ EsMiembro.
Proof.
    intro hm.
    cut (~ EsEscoces).
    - intro hnesc.
      absurd UsaMediasRojas.
      + elim (Regla2 hm).
        * intro hkilt.
          absurd EsEscoces.
          -- assumption.
          -- elim (Regla5 hm hkilt).
             intro hesc.
             intro hcas.
             assumption.
        * intro hnmr.
          assumption.
      + apply Regla1.
        * assumption.
        * assumption.
    - intro hesc.
      absurd SaleDomingos.
      + apply Regla3.
        * assumption.
        * elim (Regla5 hm (Regla6 hm hesc)).
          intro h1.
          intro h2.
          assumption.
      + elim (Regla4 hm).
        intro hsd.
        intro hes.
        apply hes.
        assumption.
Qed.

Theorem ej11ii: ~ EsMiembro.
Proof.
    tauto.
Qed.

(* Ej 12 *)
(* Definiciones *)
Variable PF:Prop. (* el paciente tiene fiebre *)
Variable PA:Prop. (* el paciente tiene piel amarillenta *)
Variable PH:Prop. (* el paciente tiene hepatitis *)
Variable PR:Prop. (* el paciente tiene rubeola *)

(* Si el paciente tiene fiebre o el paciente tiene la piel amarillenta, entonces tiene hepatitis o rubeola. *)
Hypothesis R1: (PF \/ PA) -> (PH \/ PR).
(* El paciente no tiene rubeola o tiene fiebre.  *)
Hypothesis R2: ~ PR \/ PF.
(* Si el paciente tiene hepatitis, pero no la rubeola, entonces tiene la piel amarillenta. *)
Hypothesis R3: (PH /\ ~ PR) -> PA.


Theorem ej12t: (~PA /\ PF) -> PR.
Proof.
    tauto.
Qed.
Theorem ej12: (~PA /\ PF) -> PR.
Proof.
    intro h.
    elim h.
    intro hna.
    intro hf.
    cut (PH \/ PR).
    -   intro hhor.
        elim hhor.
        +   intro hh.
            elim (classic PR).
            *   intro hr.
                assumption.
            *   intro hnr.
                absurd PA.
                --  assumption.
                --  apply R3.
                    split.
                    ++  assumption.
                    ++  assumption.
        +   intro hr.
            assumption.
    -   apply R1.
        left.
        assumption.
Qed.


(* Ej 13 *)
(* Formalización a cargo de los estudiantes *)
Variable ACuad:Prop.
Variable ANad:Prop.
Variable AHerb:Prop.
Variable AVuel:Prop.
Variable ALech:Prop.

(* • RZ 1: Los animales cuadrúpedos no nadan.  *)
Hypothesis RZ1: ACuad -> ~ ANad.
(* • RZ 2: Los animales herbívoros vuelan.  *)
Hypothesis RZ2: AHerb -> AVuel.
(* • RZ 3: Los animales son herbívoros o toman leche.  *)
Hypothesis RZ3: AHerb \/ ALech.
(* • RZ 4: Los animales vuelan o no toman leche.  *)
Hypothesis RZ4: AVuel \/ ~ALech.
(* • RZ 5: Los animales que vuelan son herbívoros y cuadrúpedos.  *)
Hypothesis RZ5: AVuel -> (AHerb /\ ACuad).
(* • RZ 6: Los animales nadan si y sólo si son herbívoros. *)
Hypothesis RZ6: ANad <-> AHerb.

Theorem ej13t: False.
Proof.
    tauto.
Qed.

Theorem ej13: False.
Proof.
    cut AHerb.
    -   intro hherb.
        absurd ANad.
        +   apply RZ1.
            elim RZ5.
            *   intro h1.
                intro h2.
                assumption.
            *   apply RZ2.
                assumption.
        +   elim RZ6.
            intro h1.
            intro h2.
            apply h2.
            assumption.
    -   elim RZ3.
        +   intro hherb.
            assumption.
        +   intro hlech.
            elim RZ4.
            *   intro hvuel.
                elim RZ5.
                --  intro h1.
                    intro h2.
                    assumption.
                --  assumption.
            *   intro hnlech.
                absurd ALech.
                --  assumption.
                --  assumption.
Qed.

End Traducciones.
