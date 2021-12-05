Require Import Setoid.

(* forall_e Hypothese t: introduit une nouvelle hypothèse qui est ce 
   qu'on obtient quand on applique Hypothese de la forme
   forall x:T, ...
   au terme t:T   *)
Ltac forall_e H t := generalize (H t); intro.

(* Alternativement:
   specialize Hypothese with t
   specialize Hypotheses with (x:=t)
   specialize Hypothese with t as Ht
   specialize Hypothese with (x:=t) as Ht
   les deux premières formes remplacent l'hypothèse;
   specifier la variable à lier avec (x:=t) permet de sélectionner
   la variable x s'il y a plusieurs quantificateurs consécutifs,
   forall z y x, ...  *)

Section Vehicules.

(* Prenez le temps de vous familiariser avec les hypothèses, et de les
   interpréter mentalement: cela vous aidera pour vos preuves *)

  Variable vehicule: Type.
  
  Variable voiture: vehicule -> Prop.
  Variable velo: vehicule -> Prop.
  Variable rouge: vehicule -> Prop.
  Variable noir: vehicule -> Prop.
  Variable blanc: vehicule -> Prop.
  Variable ford: vehicule -> Prop.
  Variables totoche T: vehicule.

  Hypothesis Htot: rouge totoche.
  Hypothesis HT: ford T.
  Hypothesis Hford: forall v, ford v -> noir v.

  Hypothesis Hcouleur: forall v, rouge v \/ noir v \/ blanc v.
  Hypothesis Hrn: forall v, ~(rouge v /\ noir v).
  Hypothesis Hnb: forall v, ~(noir v /\ blanc v).
  Hypothesis Hrb: forall v, ~(rouge v /\ blanc v).

  Hypothesis Htype: forall v, voiture v \/ velo v.
  Hypothesis Hvv: forall v, ~(voiture v /\ velo v).

  Variable propulsion: Type.
  Variable categorie: vehicule -> propulsion -> Prop.
  Variable essence : propulsion.
  Variable electrique: propulsion.  
  Variable pedale: propulsion.

  Hypothesis Hve: ~(exists v, velo v /\ categorie v essence).

    
(* Un exemple *)

  Lemma Exemple: noir T.
  Proof.
    forall_e Hford T.
    apply H; assumption.
  Qed.

(* Un second exemple *)
  Lemma Exemple_bis: forall v:vehicule, ~voiture v -> velo v.
  Proof.
    intros.
    forall_e Htype v.
    destruct H0.
    - contradiction.
    - assumption.
  Qed. 

(* Les exercices commencent ici *)

(* Dans chaque Lemme, remplacer "Admitted" par votre propre script de preuve.
   N'oubliez pas de terminer chaque preuve par "Qed". *)

  Lemma Exercice1: ~ ford totoche.
  Proof.
  Admitted.

  Lemma Exercice2: forall v:vehicule, noir v -> ~(rouge v \/ blanc v).
  Proof.
  Admitted.

  Lemma Exercice3: (forall v, velo v-> rouge v) -> (forall w, ford w -> voiture w).
  Proof.
  Admitted.

  Lemma Exercice4: ~(totoche=T).
  Proof.
  Admitted.
    
  Lemma Exercice5: (exists v, blanc v /\ voiture v) -> exists v, voiture v /\ ~ford v.
  Proof.
  Admitted.

  Lemma Exercice6 : forall v,  categorie v essence -> voiture v.
  Proof.
  Admitted.

End Vehicules.

(* Fin des exercices *)