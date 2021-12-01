Require Import Setoid.
(*  Logique intuitionniste *)

Section LJ.
 Variables P Q R S T : Prop.
 (*  Tactiques pour la conjonction 

    Introduction : pour prouver A /\ B : split (il faudra prouver A, puis B)
    Elimination : destruct H, si H : A /\ B 
                  variante : destruct H as [H1 H2].
        Dans les deux cas, on récupère deux hypothèses pour A et B (et on 
        choisit leurs noms, pour la variante "as..")
  *)
 Lemma and_comm : P /\ Q -> Q /\ P.
 Proof.
   intro H.
   destruct H as [H0 H1]. (* /\e *) 
   (* " split /\i " *)
   split;assumption. (* "assumption" résout les deux sous-buts *)
 Qed.

 (* tactiques pour la disjonction 
    Introduction:
     pour prouver A \/ B a partir de A : left
     pour prouver A \/ B a partir de B : right

    Elimination:
     preuve par cas : destruct H, si H: A \/ B
                      variante : destruct H as [H1 | H2]
        On aura a faire deux preuves, une pour chaque cas (cas A, cas B)
  *)

  Lemma or_not : P \/ Q -> ~P -> Q.
  Proof.
   intros H H0.     
   destruct H.
   - exfalso.
     apply H0; assumption.
     (* alternative: 
     assert (f:False).    
     {
       apply H0; trivial.
     }
     destruct f. *)
     (* "destruct f" sur f:False résoud n'importe quel but *)
   - assumption.
   Qed.

  (* Structuration de la preuve: +,*,+
     utiles quand on a plusieurs sous-preuves non triviales;
     améliorent la lisibilité du script *)
  
   (*  equivalence logique (<->, iff):
       unfold iff transforme A <-> B en
                             (A -> B) /\ (B -> A).
       donc split, destruct, etc, marchent

       (iff pour "if and only if", le "si et seulement si" en anglais)
    *)

  Lemma iff_comm : (P <-> Q) -> (Q <-> P).
  Proof.
    intro H.
    destruct H.
    split.
    - assumption.
    - assumption.
    (* "assumption" résoud les deux sous-buts engendrés par "split"
    donc on peut remplacer les trois dernières lignes par
    split; assumption.
    *)
  Qed.

  (* la regle de remplacement est implantée en Coq *)
  (* "rewrite H" fait un remplacement uniforme quand H est une
     équivalence *)
  (* "rewrite H" réécrit le but courant avec H *)
  (* "rewrite H in H'" fait la réécriture de H dans une autre hypothèse H' *)
  (* "rewrite <- H" réécrit dans l'autre sens, le membre droit par le gauche *)
  Lemma L1 : (P <-> Q) -> ~(Q <-> ~P).
  Proof.  
     intro H.
     rewrite H.
     intro H0.
     destruct H0.
     assert (~Q).
     { intro H2.
       apply H0; assumption.
     }
     apply H2. apply H1. assumption. 
  Qed.

  (* Fin des exemples, début des exercices *)

  (* Exercice : remplacer tauto par des vraies preuves 
     interactives *)
  (*  Exercices de la feuille 4 *)

  Lemma and_false : P /\ False -> False.
  Proof.
    intro Hpf.
    destruct Hpf.
    assumption. 
  Qed.

  Lemma and_assoc : (P /\ Q) /\ R <-> P /\ (Q /\ R).
  Proof.
    split.
    - intros.
      destruct H as [Hpq Hr].
      destruct Hpq as [Hp Hq].
      split.
      assumption.
      split;assumption.
    - intros.
      destruct H as [Hp Hqr].
      destruct Hqr as [Hq Hr].
      split.
      split;assumption.
      assumption.
  Qed.

  (* Ex. 2 *)
  Lemma or_to_imp: ~ P \/ Q -> P -> Q.
  Proof.
    intros.
    destruct H.
    absurd (P);assumption.
    assumption.
  Qed.   

  Lemma not_or_and_not: ~(P\/Q) -> ~P /\ ~Q.
  Proof.
    intros.
    split .
    (* but ~P *)
    - intro.
      apply H.
      left;assumption.
    (* but ~Q *)
    - intro.
      apply H.
      right;assumption.
  Qed.

  (* Exercice 4 *)

  Lemma absorption_or: P \/ False <-> P.
  Proof.
    split.
    - intro.
      destruct H.
      + assumption.
      + exfalso.
        assumption.
    - intro.
      left;assumption.
  Qed.

  Lemma and_or_dist : P /\ (Q \/ R) <-> P /\ Q \/ P /\ R.
  Proof.
    split.
    - intros.
      destruct H as [Hp Hqr].
      destruct Hqr.
      (* avec Q  *)
      + left.
        split;assumption.
      (* avec R *)
      + right.
        split;assumption.
    - intros.
      destruct H .
      (* avec p /\ Q *)
      + destruct H .
        split.
        * assumption.
        * left.
          assumption.
       (* avec P/\R  *)
      + destruct H.
        split.
        * assumption.
        * right.
          assumption.
  Qed.

  Lemma or_and_dist : P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
  Proof.
    split.
    - intros.
      destruct H.  
      split.
      (* avec P  *)
       left;assumption.
       left; assumption.
      (* avec (Q /\ R) *)
       destruct H.
       split.
       right;assumption.
       right;assumption.
    - intros.
      destruct H.
      destruct H.
      + left;assumption.
      + destruct H0.
        * left ; assumption .
        * right .
        split;assumption.
  Qed.

  Lemma and_not_not_impl: P /\ ~ Q -> ~(P -> Q).
  Proof.
    intros.
    intro.
    destruct H.
    apply H1.
    apply H0;assumption.
  Qed.

  Lemma de_morgan1 : ~ (P \/ Q) <-> ~P /\ ~Q.
  Proof.
    split.
    (* not_or_and_not *)
    - auto.
    - intros.
      intro.
      destruct H.
      destruct H0.
      absurd (P);assumption.
      absurd Q ;assumption .
  Qed.

  Lemma reductio_ad_absurdum: (P -> ~P) -> ~P.
  Proof.
    intro.
    intro.
    absurd P .
    - apply H ; assumption .
    - assumption.
  Qed.

  Lemma np_p_nnp: (~P -> P) -> ~~P.
  Proof.
    intro.
    intro.
    absurd P .
    - assumption.
    - apply H.
      assumption.
  Qed.

  (* Exercice: reprendre toutes les preuves précédentes, 
     en simplifiant et clarifiant les scripts:
     - structurer les sous-preuves avec +/-/*
     - inversement, quand c'est possible, factoriser avec 
       l'enchainement de tactiques (par ";")

     Le but est de faire que le script soit plus facile à lire
     par un humain, pas pour la machine.
   *)
  
End LJ.