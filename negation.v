Section Negation.
  Variables P Q R S T: Prop.

  (* unfold not: expansion de la négation dans le but *)
  (* unfold not in X: expansion de la négation dans l'hypothèse X *)
  (* exfalso: transforme le but courant en False; c'est l'équivalent
     de la règle d'élimination de la contradiction *)

  (* Executez cette preuve en essayant de comprendre le sens de chacune des nouvelles tactiques utilisées. *)
  Lemma absurde_exemple: P -> ~P -> S.
  Proof.
    intros p np.
    unfold not in np.
    exfalso.
    apply np.
    assumption.
  Qed.
  
  Lemma triple_neg_e : ~~~P -> ~P.
  Proof.
     intro H. 
     intro H0.
     apply H.
     intro H1.
     apply H1.
    assumption.
   Restart.  (* Annule la preuve en cours, et en commence un autre *)
   unfold not.
   auto.
   (* auto est une tactique qui est capable de beaucoup, mais qu'on
      s'interdira d'utiliser dans nos preuves *)
   Qed.

  (* Début des exercices *)

  (* QUESTION: Remplacer les Admitted par des scripts de preuve *)
  Lemma absurde: (P -> Q) -> (P -> ~Q) -> (P -> S).
  Proof.
    intros.
    absurd Q .
    - apply H0.
      assumption.
    - apply H.
      assumption.
  Qed.
  Check absurde.

  Lemma triple_abs: ~P -> ~~~P.
  Proof.
    intro Hnp.
    intro Hnnp. 
    apply Hnnp. (* lam |- ~~P == ~p -> _|_ *)
    assumption.
  Qed.

  Lemma absurd' : (~P -> P) -> ~~P.
  Proof.
    intro.
    intro.
    absurd P .
    (*but ~ p*)
    - assumption.
    (*but p *)
    - apply H.
      assumption.
  Qed.

  Definition Peirce  := ((P -> Q) -> P) -> P.
  Check Peirce .
  (* On va prouver non-non-Peirce *)
  Lemma Peirce_2 : ~~ Peirce.
  Proof.
    (* Strategie: sous hypothese ~Peirce [par intro], montrer ~P, puis s'en 
       servir pour montrer Peirce, et on aura une contradiction
       entre Peirce et ~Peirce *)
    intro.
    assert (np: ~P).
    {
      intro.
      apply H.
      intro.
      assumption.
    }
    apply H.
    intro.
    apply H0.
    intro.
    exfalso.
    apply np.
    assumption.
  Qed.

  (* Une série de séquents à prouver; à chaque fois, il faut
  l'énoncer, en introduisant les hypothèses au moyen d'une
  sous-section. *)

  (* P->Q, R->~Q, P->R |- P->S *)
  Section myT01.
    Hypothesis H: P->Q.
    Hypothesis H0: R->~Q.
    Hypothesis H1: P->R.

    Lemma my_01: P->S.
      Proof.
      intro .
      absurd Q.
      (* but ~Q *)
      - apply H0.
        apply H1.
        assumption.
      (*but Q*)
      - apply H.
        assumption. 
      Qed.
  End myT01.

  (* ~P->~Q |- ~~Q->~~P *)
  Section myT02.
    Hypothesis H: ~P->~Q.

    Lemma my_02: ~~Q->~~P.
      Proof.
        intro.
        intro.
        absurd (~Q).
        - assumption.
        - apply H.
          assumption.
      Qed.
  End myT02.

  (* P->~P |- ~P *)
  Section myT03.
    Hypothesis H: P->~P.

    Lemma my_03:  ~P.
      Proof.
        intro .
        absurd P.
        - apply H.
          assumption.
        - assumption.
      Qed.
  End myT03.

  (* ~~P |- ~P->~Q *)
  Section myT04.
    Hypothesis H: ~~P.

    Lemma my_04: ~P -> ~Q.
      Proof.
        intro.
        absurd (~P);assumption.
      Qed.
  End myT04.
  (* P->~Q, R->Q |- P->~R *)
  Section myT05.
    Hypothesis H:P->~Q.
    Hypothesis H0: R->Q.

    Lemma my_05: P->~R.
      Proof.
        intro.
        intro.
        absurd Q.
        (*but ~Q*)
        - apply H.
          assumption.
        (*but Q*)
        - apply H0.
          assumption. 
      Qed.
  End myT05.

  (* ~(P->Q) |- ~Q *)
  Section myT06.
    Hypothesis H:~(P->Q).
    Lemma my_06: ~Q.
      Proof.
        intro.
        apply H.
        intro.
        assumption.
      Qed.
  End myT06.

  (* Séquents proposés en test par le passé *)

  Section Test01.
    Hypothesis H: P->Q.
    Lemma Ex01: ~(~Q->~P) -> R.
    Proof.
      intro.
      absurd (P->Q).
      (*but ~ P->Q *)
      - intro.
        apply H0.
        intro.
        intro.
        apply H2.
        apply H.
        assumption.
        (* absurd Q.
        * assumption.
        * apply H.
          assumption. *)
      (*but  P->Q *)
      - assumption .
    Qed.
  End Test01.

  Section Test02.
    Hypothesis H: ~(P->R).

    Lemma Ex02: Q->(P->Q->R)->P.
    Proof.
      intros.
      absurd (P->R).
      - assumption.
      - intro.
        apply H1;assumption. 
    Qed.
    
  End Test02.

  Section Test03.
    Hypothesis H: ~(Q->R).

    Lemma Ex03: (P->Q->R)->(P->Q).
      Proof.
        intros.
        absurd (Q->R).
        - assumption .
        - apply H0;assumption. 
      Qed.
  End Test03.

  Section Test04.
    Hypothesis H: ~~P.

    Lemma Ex04: Q->(P->Q->False)->P.
    Proof.
      (* intros.
      exfalso.
      apply H.
      - exfalso.
        apply H1. 
       *)
    Qed.
  End Test04.
    
End Negation.


