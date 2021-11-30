Require Import Setoid Classical.

(*  Logique classique
    On peut sauter les 2 commandes suivantes 
 *)

(* un peu de magie noire *)
Definition EXM :=   forall A:Prop, A \/ ~A.

Ltac add_exm  A :=
  let hname := fresh "exm" in
  assert(hname : A \/ ~A);[classical_right; assumption|].


Section LK.
  (* 
   Pour ajouter une instance du tiers-exclu de la forme  A \/ ~A 
   il suffit d'exécuter la tactique "add_exm A"
   *)

  Variables P Q R S T : Prop.

  Lemma double_neg : ~~ P -> P.
  Proof.
    intro H.
    add_exm  P. (* "je fais un tiers exclus sur P " *)
    destruct exm. (* Presque toujours, destruct suit add_exm *)
    - assumption.
    - assert (f:False).
      {
        apply H; assumption.
      }
      destruct f. (* ou: exfalso, etc. *)
   Qed.

  (* Variantes: tactiques classical_left et classical_right.
     Pour prouver A \/ B:
     - classical_left demande de prouver A, avec ~B comme hypothèse en plus.
     - classigal_right demande de prouver B, avec ~A comme hypothèse en plus.
  *)

  Lemma weak_exm: P \/ (P->Q).
  Proof.
  classical_right.
  intro p; exfalso; apply H; assumption.
  Qed.

  (* Exercice: completer toutes les preuves, en remplaçant les
     "Admitted" par des preuves terminées par "Qed."; et 
     sans utiliser ni auto, ni tauto.  *)

  Lemma de_morgan : ~ ( P /\ Q) <-> ~P \/ ~Q.
  Proof.
  Admitted.

  Lemma not_impl_and : ~(P -> Q) <-> P /\ ~ Q.
  Proof.
  Admitted.

  Lemma contraposee: (P -> Q) <-> (~Q -> ~P).
  Proof.
  Admitted.

  Lemma exm_e : (P -> Q) -> (~P -> Q) -> Q.
  Proof.
  Admitted.

  Lemma exo_16 : (~ P -> P) -> P.
  Proof.
  Admitted.

  Lemma double_impl : (P -> Q) \/ (Q -> P).
  Proof.
  Admitted.

  Lemma imp_translation : (P -> Q) <-> ~P \/ Q.
  Proof.
  Admitted.

  Lemma Peirce : (( P -> Q) -> P) -> P.
  Proof.
  Admitted.

  (* Quelques exercices d'anciens tests *) 
  Lemma test_1: (P->Q)->(~P->R)->(R->Q)->Q.
  Proof.
  Admitted.

  Lemma test__2: (P \/ (Q\/R))-> (~P) -> (~R) -> (P\/Q).
  Proof.
  Admitted.

  Lemma test_3: (~P-> Q/\R)->(Q->~R)->P.
  Proof.
  Admitted.

  Lemma test_4: (~P->Q)->(~Q\/R)->(P->R)->R.
  Proof.
  Admitted.

  Lemma test_5: (P->Q)->(~P->~Q)->((P/\Q) \/ ~(P\/Q)).
  Proof.
  Admitted.

  Lemma test_6: (P->Q)->(~P->Q)->(Q->R)->R.
  Proof.
  Admitted.

End LK.

Section Club_Ecossais. (* version propositionnelle *)
  Variables E R D M K: Prop.
  (* Ecossais, chaussettes Rouges, sort le Dimanche, Marié, Kilt *)

  Hypothesis h1: ~E -> R.
  (* Tout membre non ecossais porte des chaussettes rouges *)
  Hypothesis h2: M -> ~D.
  (* Les membres maries ne sortent pas le dimanche *)
  Hypothesis h3: D <-> E.
  (* Un membre sort le dimanche si et seulement si il est ecossais *)
  Hypothesis h4: K -> E /\ M.
  (* Tout membre qui porte un kilt est ecossais et est marie *)
  Hypothesis h5: R -> K.
  (* Tout membre qui porte des chaussettes rouges porte un kilt *)
  Hypothesis h6: E -> K.
  (* Tout membre ecossais porte un kilt. *)

  Lemma personne: False. (* Le club est vide! *)
  Proof.
  Admitted.

End Club_Ecossais.  
  
(** On peut sauter cette section *)

(* Au sens strict, cette partie est hors programme; il s'agit de voir que 
   diverses hypothèses (toutes formulées "au second ordre": avec des 
   quantificateurs universels sur des propositions)
   sont équivalentes, et correspondent à la logique classique *)
(* ATTENTION: pour que ces exercices aient un sens, il faut les faire SANS
   utiliser les tactiques réservées à la logique classique (add_exm, ou
   classical_left, ou classical_right *)
Section Second_ordre. 
  Definition PEIRCE := forall A B:Prop, ((A -> B) -> A) -> A.
  Definition DNEG := forall A, ~~A <-> A.
  Definition IMP2OR := forall A B:Prop, (A->B) <-> ~A \/ B.

  Lemma L2 : IMP2OR -> EXM.
  Proof.
    unfold IMP2OR, EXM.
    intros.
    assert (~ A \/ A).
    rewrite <- H. (* Coq "voit" qu'il suffit de prendre B=A; il va falloir prouver A->A *)
  Admitted.
  

  Lemma L3 : EXM -> DNEG.
  Proof.
    unfold DNEG , EXM.
    intros.
    (* H permet de faire un tiers exclus sur A *)
    assert (H0: A \/ ~A).
    {
      admit.
    }
  Admitted.

  Lemma L4 : PEIRCE -> DNEG.
  Proof.
    unfold DNEG , PEIRCE.
  Admitted.
  
  Lemma L5 : EXM -> PEIRCE.
  Proof.
  Admitted.

End Second_ordre.


  