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
Admitted.

Lemma autre_contraposee: (P->~Q) -> (Q->~P).
Proof.
Admitted.

Lemma DS1: ((P->Q)->R)->((~P->~Q)->~R)->(P->Q->S).
Proof.
Admitted.

Lemma DS2: (P->Q)->~(R->Q)->(~R->S) -> (R->P->S).
Proof.
Admitted.

(* Ne pas foncer sans réfléchir *)
Lemma piege: (P->~Q)->(~Q->R)->(R->~S)->(~S->~P) -> ~P.
Proof.
intros.
(* à compléter *)
Admitted.

End Complements_Negation.

Section Double_Negation.
(* Autour de la double négation *)
Variables P Q: Prop.
(* De P, on peut déduire non-non-P *)
Lemma dn_i: P-> ~~P.
Proof.
Admitted.

(* On a prouvé dans absurd' (fichier negation.v), que, de "non-P implique P",
   on peut déduire, peut-être pas P, mais au moins non-non-P *)

(* Si on suppose, ce qui est plus fort, qu'on peut déduire P
   de "non-P implique P", alors on peut justifier l'élimination de
   la double négation [pour P] *)
Lemma trop_de_negations: ((~P->P)->P) -> (~~P -> P).
Proof.
Admitted.

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
  
  End Sequent3.

End Preuves_de_sequents.