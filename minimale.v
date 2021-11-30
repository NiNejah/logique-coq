(* Raccourcis clavier de coqide *)
(* CTRL-flèche bas: avancer d'une commande *)
(* CTRL-flèche haut: revenir en arrière d'une commande *)
(* CTRL-flèche droit: avancer ou revenir en arrière jusqu'au curseur *) 

(** premiers pas en Coq *)

(* Logique minimale "pure": pas de négation/contradiction *)

Section Exercices.

  Variables P Q R S T : Prop.

  (* Une Section peut contenir d'autres [sous-]Sections. C'est le bon endroit
     pour definir des hypotheses (et donc prouver des sequents avec hypotheses).

     Dans ce fichier, la section "Exercices" va jusqu'au bout *)
  
  Lemma imp_dist: (P -> Q -> R) -> (P -> Q) -> P -> R.
  Proof.
    intro Hpqr.
    intro Hpq.
    intro Hp.
    apply Hpqr.
    - assumption.
    - apply Hpq.
      assumption.
  Qed.

  (* Explication des tactiques utilisées: *)
  (* intro: utilisation de la regle d'introduction pour changer de but *)
  (* apply: utilisation d'une implication qui a la bonne conclusion
     (il va falloir prouver ses hypotheses) *)
  (* Note: on ne peut faire "apply" que sur une propriété déjà prouvée,
     contrairement au modus ponens des preuves en arbres *)
  (* C'est automatiquement un modus ponens: "apply Hpqr" pour prouver R
     demande à prouver P et Q *)
  (* assumption: utilisation de la regle d'hypothese *)

  Check imp_dist.  (* On voit la formule prouvée *)
  Print imp_dist.  (* Pour voir le "terme de preuve" calculé *)
  (* la syntaxe est très proche de celle de Ocaml *)

  (* exemple de preuve d'un sequent avec hypothèses *)

  Section S1.
    Hypothesis H : P -> Q.
    Hypothesis H0 : P -> Q -> R.

    Lemma L2 : P -> R.
    (* le sequent est: P->Q, P->Q->R |- P->R *)
    Proof.
      intro p.
      apply H0.
      - assumption.
      - apply H.
        assumption.
    Qed.

    Check L2. (* Les hypothèse font partie de la section *)
  End S1.

  (* Quand on ferme la section, ses hypotheses sont "exportees" sous la
     forme d'hypotheses supplementaires pour L2                         *)
  Check L2.

  
  Section About_cuts.
    Hypothesis H : P -> Q.
    Hypothesis H0 : P -> Q -> R.
    Hypothesis H1 : Q -> R -> S.
    Hypothesis H2 : Q -> R -> S -> T.

    (* preuve sans lemme (coupure) *)
    Lemma L3 : P -> T.
    (* QUESTION: Quel est le séquent qu'on s'apprête à prouver? *)
    (* REPONSE : (P -> Q),(P -> Q -> R),(Q -> R -> S),(Q -> R -> S -> T ) |- P -> T*)
    (* QUESTION: Faites-en une preuve papier AVANT de continuer *)
    Proof.
      intro p.
      apply H2.
      - apply H.
        assumption.
      - apply H0.
        + assumption.
        + apply H.
          assumption.
      - apply H1.
        + apply H. 
          assumption.
        + apply H0.
          * assumption.
          * apply H. 
          assumption.
    Qed.
    (* QUESTION: Réécrivez le script ci-dessus en introduisant des tirets 
       (-, *, +) à chaque fois qu'une tactique engendre plus d'un 
       sous-but *)
    
    (* preuve avec coupures: on prouve Q et R une seule fois chacun,
       puis on les utilise *)

     Lemma L'3 : P -> T.
     Proof.
       intro p.
       assert (q: Q). { 
         apply H. assumption.
         }
       (* On a fini de prouver Q; on a maintenant une hypothèse (q:Q) *)   
       assert (r: R). {
         apply H0.
         - assumption.
         - assumption.
          }
       (* Pareil: on a maintenant prouvé R, et on a gagné une hypothèse *)
       assert (s : S). {
        apply H1. assumption. assumption.
       }
       apply H2; assumption. (* sans le ; il faut trois "assumption" *)
     Qed.

     (* assert: permet d'ouvrir une nouvelle sous-preuve, *)
     (* dans laquelle on se définit un nouveau but; c'est *)
     (* une coupure. Les accolades sont optionnelles mais *)
     (* facilitent la lecture humaine                     *)
     
     Check L'3.

(* remarquez la différence entre les termes de preuves avec coupure et sans coupure. *)
     Print L'3.
     Print L3.
(* Les coupures deviennent des "let.. in.." similaires à ceux de Ocaml *)

  End About_cuts.


 (* Exercices 

    Reprendre les exemples vus en TD, en utilisant les tactiques 
    assumption, apply, assert et intro/intros.

    Remplacer chaque commande Admitted par un script correct de preuve,
    suivi de la commande Qed.

  *)

  Lemma IdP : P -> P.
  Proof.
   intro hP.
   assumption.
  Qed.

  Lemma IdPP : (P -> P) -> P -> P.
  Proof.
  intros HPP Hp.
  assumption.
  Qed.

  (* sans regarder le fichier de demo, c'est de la triche *)
  Lemma imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
  Proof.
    intros Hpq Hqr Hp.
    apply Hqr.
    apply Hpq.
    assumption.
  Qed.

  Section proof_of_hyp_switch.
    Hypothesis H : P -> Q -> R.
    Lemma hyp_switch : Q -> P -> R.
    Proof.
      intros Hq Hp.
      apply H;assumption.
    Qed.
  End proof_of_hyp_switch.

  Check hyp_switch.

  Section proof_of_add_hypothesis.
    Hypothesis H : P -> R.

    Lemma add_hypothesis : P -> Q -> R.
    Proof.
      intros Hp Hq.
      apply H. assumption.
    Qed.

  End proof_of_add_hypothesis.

  (* prouver le sequent (P -> P -> Q) |- P -> Q  
     (il faut l'énoncer, et faire la preuve) 
      *)
  Section proof_of_remove_dup_hypothesis. 
      (*TODO : (P -> P -> Q) |- P -> Q *)
      Hypothesis H: P -> P -> Q.
      Lemma my_hyp: P->Q.
      Proof.
        intro Hp.
        apply H;assumption.
      Qed.

  End proof_of_remove_dup_hypothesis.


  (* même exercice avec le séquent P->Q |- P->P->Q *)
  Section proof_of_dup_hypothesis.
        Hypothesis H: P -> Q.
        Lemma my_hyp_2: P->P->Q.
        Proof.
          intros.
          apply H;assumption.
        Qed.
        
  End proof_of_dup_hypothesis.

  (* meme exercice avec 
     P -> Q , P -> R , Q -> R -> T |- P -> T  
   *)
  Section proof_of_distrib_impl.
    Hypothesis H : P -> Q.
    Hypothesis H0: P -> R.
    Hypothesis H1: Q -> R -> T.
    Lemma hyp3:P->T .
    Proof.
      intro Hp.
      apply H1.
      - apply H.          (*but Q*) 
        assumption.
      - apply H0.         (*but R*) 
        assumption.  
    Qed.
    

  End proof_of_distrib_impl.

  (* même exercice, avec 
     P->Q, Q->R, (P->R)->T->Q, (P->R)->T |- Q   
     (ex. 9 de la feuille "Logique minimale")
   *)
  Section proof_of_ex9.
    Hypothesis H : P->Q . 
    Hypothesis H0: Q->R . 
    Hypothesis H1:(P->R)->T->Q .
    Hypothesis H2:(P->R)->T  .
    Lemma trouve_q: Q.
    Proof.
      assert (Hpr: P -> R ). {   (*but P->R*)
      intro hp.
      apply H0.
      apply H;assumption.
      }
      apply H1.
      - assumption.
      - apply H2. assumption.
    Qed.
    
  End proof_of_ex9.
  
  (* exercice 10 de la feuille "Logique minimale" *)
  Section Proof_of_weak_Peirce.

    Hypothesis H: (((P->Q)->P)->P)-> Q.
    Lemma weak_Peirce : Q.
    Proof.
      apply H.
      intro.
      apply H0.
      intro.
      apply H.
      intro.
      assumption .
    Qed.

  End Proof_of_weak_Peirce.
  Check weak_Peirce.
  Print weak_Peirce. (* Pas facile à déchiffrer *)
  (* QUESTION: si vous n'aviez pas déjà fait cet exercice sur papier, 
     écrivez une preuve papier du même séquent; votre script de preuve
     devrait vous aider à identifier quelle règle utiliser à chaque étape
  *)

End Exercices.

  
     