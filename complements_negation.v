(* Consigne générale: structurer proprement vos scripts de preuve;
   chaque fois qu'une tactique produit plus d'un but, utiliser des
   puces pour séparer les preuves des deux buts.

   Vous pouvez aussi essayer, autant que possible, d'enchaîner les
   tactiques au moyen de points-virgules.
*)

(* Tous les "Admitted" doivent être remplacés par vos scripts de preuves. *)

(* Quelques lemmes à prouver *)
Section Complements_Negation.
Variables P Q R S: Prop.

Lemma contraposee: (P->Q) -> (~Q->~P).
Proof.
   intros.
   unfold not .
   intro.
   absurd(Q).
   -assumption.
   - apply H.
      assumption.
Qed.

Lemma autre_contraposee: (P->~Q) -> (Q->~P).
   Proof.
      intros.
      intro.
      absurd Q.
      - apply H.
         assumption.
      -assumption.
   Qed.

Lemma DS1: ((P->Q)->R)->((~P->~Q)->~R)->(P->Q->S).
   Proof.
      intros.
      exfalso.
      apply H0.
      - intro.
         absurd P;assumption.
      - apply H.
         intro.
         assumption.
   Qed.

Lemma DS2: (P->Q)->~(R->Q)->(~R->S) -> (R->P->S).
   Proof.
   intros.
   assert (Hq : Q ).
   {
      apply H.
      assumption.
   }
   assert(Hrq : R->Q).
   {
      intro.
      assumption.
   }
   absurd (R->Q);assumption.
   Qed.

(* Ne pas foncer sans réfléchir *)
Lemma piege: (P->~Q)->(~Q->R)->(R->~S)->(~S->~P) -> ~P.
   Proof.
   intros.
   intro.
   apply H2.
   (* pour ~S *)
   - apply H1.
     apply H0.
     apply H.
     assumption.

   (* pour P   *)
   - assumption.  
   Qed.

End Complements_Negation.

Section Double_Negation.
(* Autour de la double négation *)
Variables P Q: Prop.
(* De P, on peut déduire non-non-P *)
Lemma dn_i: P-> ~~P.
   Proof.
      intro.
      intro.
      absurd P;assumption.
   Qed.

(* On a prouvé dans absurd' (fichier negation.v), que, de "non-P implique P",
   on peut déduire, peut-être pas P, mais au moins non-non-P *)

(* Si on suppose, ce qui est plus fort, qu'on peut déduire P
   de "non-P implique P", alors on peut justifier l'élimination de
   la double négation [pour P] *)
Lemma trop_de_negations: ((~P->P)->P) -> (~~P -> P).
   Proof.
      intros.
      apply H.
      intro.
      exfalso.
      apply H0.
      assumption.
   Qed.  

End Double_Negation.


Section Preuves_de_sequents.
Variables P Q R S: Prop.
(* Les exercices restants consistent à formuler soi-même les lemmes:
   chaque séquent à prouver va constituer une sous-section, avec ses
   hypothèses *)

(* Et bien sûr, faire la preuve ensuite! *)


(* Exemple *)
  Section Exemple.
  (* Séquent à prouver: P->Q, P->~Q |- P->R *)
  Hypothesis H: P->Q.
  Hypothesis H1: P->~Q.
  Lemma exemple: P->R.
  Proof.
  intro p. exfalso.
  apply H1.
  - assumption.
  - apply H. assumption.
  Qed.
  End Exemple.

  Section Sequent1.
  (* Séquent à prouver: 
     (P->Q)->~Q |- (P->Q)->~P
  *)
   Hypothesis H:(P->Q)->~Q .
   Lemma  S1:(P->Q)->~P.
   Proof.
      intro.
      intro.
      apply H.
      -assumption .
      - apply H0.
         assumption .
   Qed.
   

  End Sequent1.

  Section Sequent2.
  (* Séquent à prouver:
     (P->Q)->R, (P->Q)->~R |- Q->S
  *)
  
  End Sequent2.

  Section Sequent3.
  (* Séquent à prouver:
     P->Q, ~P->Q |- ~~Q
  *)
   Hypothesis H :P->Q.
   Hypothesis H0 :~P->Q.
   Lemma S2: ~~Q.

   Proof.
      intro.
      apply H1.
      apply H0.
      intro.
      absurd Q .
      - assumption.
      - apply H;assumption.
      (* apply H1.
      apply H;assumption. *)
Qed.
    
  End Sequent3.

End Preuves_de_sequents.