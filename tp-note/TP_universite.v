Require Import Setoid.

(* forall_e Hypothese t: introduit une nouvelle hypothèse qui est ce 
   qu'on obtient quand on applique Hypothese de la forme
   forall x:T, ...
   au terme t:T   *)
Ltac forall_e H x:= generalize (H x); intro.

(* Alternativement:
   specialize Hypothese with t
   specialize Hypotheses with (x:=t)
   specialize Hypothese with t as Ht
   specialize Hypothese with (x:=t) as Ht
   les deux premières formes remplacent l'hypothèse;
   specifier la variable à lier avec (x:=t) permet de sélectionner
   la variable x s'il y a plusieurs quantificateurs consécutifs,
   forall z y x, ...  *)

Section Universite.

(* Prenez le temps de vous familiariser avec les hypothèses, et de les
   interpréter mentalement: cela vous aidera pour vos preuves *)

Variable cours: Type.
Variable individu: Type.

Variables etudiant professeur: individu -> Prop.

Variable connait: individu -> individu -> Prop.
Variables enseigne etudie: individu -> cours -> Prop.

Variables Alice Bob Charlie Diana: individu.
Variable Anglais: cours.

Hypothesis Huniv: forall x, professeur x \/ etudiant x.
Hypothesis Hetud_prof: forall c x y, enseigne x c -> etudie y c -> connait y x.
Hypothesis cours_pas_vide: forall c, exists y, etudie y c/\ ~professeur y.
Hypothesis cours_prof: forall c, exists x, enseigne x c.
Hypothesis enseignant: forall c x, enseigne x c -> professeur x.
Hypothesis All_english: forall x, etudiant x -> etudie x Anglais.
Hypothesis Etud_se_connaissent: forall x y c, etudie x c -> etudie y c -> connait x y.

Hypothesis Ha: etudiant Alice.
Hypothesis Hb: ~ professeur Bob.
Hypothesis Hc: forall x, connait x Charlie -> professeur x.
Hypothesis Hac: connait Alice Charlie.
Hypothesis Hd: enseigne Diana Anglais.

(* Un exemple *)

Lemma Exemple: etudiant Bob.
Proof.
  forall_e Huniv Bob.
  destruct H.
  - contradiction.
  - assumption.
Qed.

(* Les exercices commencent ici *)

(* Dans chaque Lemme, remplacer "Admitted" par votre propre script de preuve.
   N'oubliez pas de terminer chaque preuve par "Qed". *)

Lemma Exercice1: connait Alice Diana.
Proof.
Admitted.

Lemma Exercice2: connait Alice Bob.
Proof.
Admitted.

Lemma Exercice3: exists x, professeur x /\ forall y, etudiant y -> connait y x.
Proof.
Admitted.

Lemma Exercice4: forall x y, professeur x \/ professeur y \/ connait x y.
Proof.
Admitted.

Lemma Exercice5: exists x, professeur x /\ etudiant x.
Proof.
Admitted.

Lemma Exercice6: forall c, ~enseigne Charlie c.
Proof.
Admitted.

End Universite.

(* Fin des exercices *)
