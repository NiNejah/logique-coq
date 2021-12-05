(* Logique du premier ordre *)

(** Tactiques :
  pour forall :  
    introduction : 
            intro, intros.
    elimination :
            apply, eapply, specialize.
            (H x ...)

  pour exists : 
     introduction: exists (fournir le terme)
     elimintation: destruct.

  pour = reflexivity (introduction),
         rewrite H   [in HØ] (elimination)
         rewrite <- H [in H0]
                  
 *)

(* tactique maison pour eliminer un forall *)
(* il faut fournir le terme temoin *)

Ltac forall_e H t := (generalize (H t); intro).

(* Exemple *)

Example E0 : ~(forall x:nat, x <> x).
Proof.
  intro H.                                       
  forall_e H 42.
  unfold not in H0.
  apply H0.
  reflexivity.
Qed.

Section Syllogismes. (* Entrainements *)
  Variable Etre: Type.
  Variables humain mortel animal : Etre -> Prop.

  Variable Socrate : Etre.
  Variable Rhino : Etre.

  Hypothesis HM : forall x,  humain x -> mortel x.
  Hypothesis HSocrate : humain Socrate.
  Hypothesis Etre_disj : forall x:Etre,  humain x \/ animal x.
  Hypothesis Hrhino : ~ humain Rhino.

  Lemma Syllogisme :  mortel Socrate.
  Proof.
    apply HM. (* elimination du forall et modus-ponens *)
    assumption.
  Qed.

  Lemma contraposee : forall x, ~ mortel x -> ~ humain x.
  Proof.  
    (* intro.
    intro.
    intro.
    apply H.
    apply HM.
    assumption. *)
    intros x Hx H.
    unfold not in Hx.
    apply Hx.
    apply HM; assumption.
  Qed.    

  Lemma Lmortel: exists x, mortel x.
  Proof.  
   exists Socrate.  (* introduction de l'existentiel *)
   apply Syllogisme. (* On peut appliquer un théorème déjà prouvé *)  
  Qed.


  Lemma Lanimal: exists x, animal x.
  Proof.  
    exists Rhino.
    destruct (Etre_disj Rhino).
    (* elimination sur la disjonction "Etre_disj" appliquée à Rhino *)
    (* On pourrait aussi utiliser forall_e *)
    - contradiction.
    - assumption.
  Qed.

  Lemma L : ~(exists x:Etre,  ~ humain x /\ ~ animal x).
  Proof.
    intro H.
    destruct H as [e He]. (* elimination de l'existentiel *)
    destruct He.
    forall_e Etre_disj e.
    destruct H1.
    - contradiction.
    - contradiction.
  Qed.

End Syllogismes.

Section Egalite. (* Entrainements, sur l'egalite *) 
  Variable A : Type.
  Variable f : A -> A.

  Lemma Egal1 : forall x:A, exists y: A, x=y.
  Proof.
   intros x.
   exists x.
   reflexivity. 
   Qed.

  Lemma Egal2 : forall x y z: A, x = y -> y = z -> x = z.
  Proof.
    intros x y z H H0.
    rewrite H.
    assumption.
  Qed. 

  (* x <> y est une abréviation de ~ (x = y) *)
  (* "unfold not" va faire apparaître l'implication vers False *)

  Lemma diff_eq : forall x y z:A, x <> y -> y = z -> x <> z.
  Proof.  
    intros.
    rewrite H0 in H.
    assumption. 
  Qed.
  
  (* À vous ! *)
  Lemma Egal3 : forall x y z: A , x = y -> x <> z -> z <> y.
  Proof.
  intros.
  rewrite H in H0 .
  (* unfold not. *)
  intro.
  rewrite H1 in H0.
  contradiction.
  (* Ou bien : 
  apply (diff_eq y z x) .
  -assumption. 
  - rewrite H.
    assumption.
  - rewrite H.
    reflexivity. *)
  Qed.

  Lemma L4 : forall x y:A, f x <> f y -> x <> y.
  Proof.
    intros.
    intro.
    rewrite H0 in H.
    contradiction.
  Qed.

End Egalite.

(* Quelques preuves de logique du premier ordre *)

(* Supprimer les "Admitted" (on admet la preuve complète) et les "admit" 
   (on admet le but courant) dans toutes les preuves qui suivent, et les
   compléter *)

Section QuelquesPreuves.
  Variable A B: Type.
  Variables P Q : A -> Prop.
  Variable R : A -> B -> Prop.
  Variable X : Prop.

  Lemma Question1 : (forall x:A, P x /\ Q x) <->
                    (forall x:A, P x) /\ (forall x:A, Q x).
  Proof.
    split; intro H.
    - split.
      + intro x.
        destruct (H x).
        assumption.
      + intro x; destruct (H x); trivial.
    -  intro x; split.
      + destruct H as [Hp Hq].
        apply Hp.
      + destruct H.
        apply H0.
  Qed.

  Lemma Question2 : (forall x, P x) \/ (forall x, Q x) ->
                    forall x, P x \/ Q x.
  Proof.
    intro.
    intro x .
    destruct H .
    - left .
      apply H.
    - right .
      apply H.
  Qed.
  
  Lemma Question3 : (exists x:A, P x /\ Q x) ->
                    (exists x:A, P x) /\  (exists x:A, Q x).
  Proof.
    intro.
    split.
    - destruct H.
      exists x.
      destruct H.
      assumption.
    - destruct H.
      destruct H.
      exists x.
      assumption.
  Qed.

  Lemma Question4 : (exists x:A, P x \/ Q x) <->
                    (exists x:A, P x) \/   (exists x:A, Q x).
  Proof.  
    split.
    - intro.
      destruct H.
      destruct H.
      * left.
          exists x.
          assumption.
      * right .
        exists x.
        assumption. 
    - intro.
      destruct H.
      destruct H.
      * exists x.
        left .
        assumption.
      * destruct H.
        exists x.
        right.
        assumption. 
  Qed.

  Section Question5.
    Hypothesis H : forall x, P x -> Q x.
    Hypothesis H0 : exists x, P x.

    Lemma L5 : exists x, Q x.
    Proof.
      destruct H0.
      exists x.
      apply H.
      assumption.
    Qed.
    (* Admitted. *)

  End Question5.
 
  (* Attention au parenthésage *)
  Lemma Question6 : forall x,  P x -> exists y,  P y.
  Proof.
    intros.
    exists x.
    assumption. 
  Qed.
 
  Lemma Question7 : ~(exists x, P x) <-> forall x, ~ P x.
  Proof.
    split.
    - intro.
      intro.
      intro.
      apply H.
      exists x.
      assumption.
    - intros.
      intro.
      destruct H0.
      absurd (P x).
      apply H.
      assumption.

  Qed.                                      

  (* Ici, X joue le rôle de n'importe quelle proposition où x n'est
     pas libre *)
  Lemma Question8 : ((exists x, P x) -> X) <->
                     forall x, P x -> X.
          
  Proof.
    split.
    - intros.
      apply H.
      exists x.
      assumption.
    - intro.
      intro.
      destruct H0.
      forall_e H x.
      apply H1.
      assumption.
  Qed.
  (* Admitted. *)

  Lemma Question9 :  (exists x:A, forall y:B, R x y)
                      -> (forall y:B, exists x:A, R x y).
  Proof. 
    intro.
    intro.
    destruct H .
    exists x.
    forall_e H y.
    assumption.
  Qed.

  (* Sur l egalite *)
  Lemma eq_sym : forall x y:A, x = y -> y = x.
  Proof.
    intros x y H.
    rewrite H.     
    reflexivity.
  Qed.

  Lemma eq_trans : forall x y z:A, x = y -> y = z -> x = z.
  Proof.
    intros.
    rewrite H.
    assumption.
  Qed.

End QuelquesPreuves.

Section TypeVide.
(* Dans cette section, on envisage la possibilité que le type A soit vide *)
  Variable A: Type.
  Variable P: A->Prop.

  Definition A_est_vide := forall x:A, x <> x.

  
  Lemma TV1 : A_est_vide -> forall x:A, P x.
  Proof.
    unfold A_est_vide. (* A compléter *)
    intro.
    intro.
    exfalso.
    forall_e H x.
    unfold not in H0.
    apply H0.
    reflexivity.
  Qed.

  Lemma TV2 : (forall x y:A, x <> y) -> A_est_vide.
  Proof.
    intros.
    unfold A_est_vide.
    intro.
    unfold not.
    intro.
    forall_e H x.
    forall_e H1 x.
    contradiction.
  Qed.

End TypeVide.


(* On passe maintenant en logique classique *)
Require Import Classical.


Section classic.
  Variable A: Type.
  Variables P Q: A->Prop.

  Hypothesis exm: forall X:Prop, X \/ ~X.

  Ltac add_exm  P :=
  let hname := fresh "exm" in
  assert(hname : P \/ ~P); [classical_right; assumption|].

(* ne pas essayer de comprendre :
   applique le raisonnement par l'absurde classique 

   Transforme un but  "Gamma |- P " en 
                      "Gamma, ~P |- False" *)

  Ltac absurdK :=
    match goal with |- ?X =>
                    let hname := fresh "exm" in
                    assert(hname := exm  X);
                      destruct hname;[assumption| elimtype False]
    end.

  Lemma Classical_Question1 : ~ (forall x, P x) <-> exists x, ~ P x.
  Proof.   
    split; intro H.
    - absurdK.
      destruct H.
      intro.
      (* start  *)
      absurdK.
      apply H0.
      exists x.
      assumption.
     (* end  *)
    - destruct H.
      intro.
      apply H.
      apply H0.
  Qed.


    (* Admitted. finir la preuve; l'autre sens est intuitionniste *)

  (* Dans le même esprit *)
  Lemma Classical_Question2: ~(forall x, P x /\ Q x) <-> exists x, ~ P x \/ ~ Q x.
  Proof.
    split.
    - intro.
      absurdK.
      destruct H.
      intro.
      split. (* pour P x /\ Q x : - P x ; - Q x*)
       (* prouve de P  *)
      + absurdK .
        destruct H0.
        exists x.
        left.
        assumption.
        (* prouve de Q *)
      + absurdK .
        destruct H0.
        exists x.
        right .
        assumption. 
    - intro .
      (* absurdK . *)
      intro.
      destruct H.
      destruct H.
      apply H.
      apply H0.
      apply H.
      apply  H0.
  Qed.


(* On complète la section "TypeVide", mais en classique *)
(* Pour des raisons techniques, le type s'appelle B *)

Section TypeVideClassique.
  Variable B: Type.
  Variable PP: B->Prop.

  Definition B_est_vide := forall x:B, x <> x.

  Hypothesis H : ~ B_est_vide.
  Hypothesis H0 : forall x:B, PP x.
    
  Lemma forall_to_exists : exists x:B, PP x. (* PAS difficile *)
  Proof.
    unfold B_est_vide in H.
    assert (exists x:B, x = x).
    { absurdK. 
      destruct H.
      intro. (*x <> x*) 
      absurdK.
      apply H1.
      exists x.
      reflexivity.
    }
    exfalso .
    apply H.
    intro.
    (* destruct H1 as [x0 Hxx]. *)
    unfold not .
    intro.
    auto.
  (*"not finiched"*)
  Admitted.
    (* absurdK. *)


    (* Compléter la preuve, y compris le "admit" *)

End TypeVideClassique.
    

Section drinkers_problem. (* Problème du buveur *)
  (* On se place en logique classique: on reprend donc le tiers exclus
     et l'absurde classique *)

  (* On va prouver le théorème CLASSIQUE suivant: dans un bar qui contient
     au moins une personne (le patron), il existe une personne qui, si elle
     boît, tout le monde boit *)

  (* Attention au semi-piège: ce n'est pas forcément le patron *)

  Variable people : Type.
  Variable patron : people.

  Variable boit : people -> Prop.
  Theorem buveurs :
    exists p:people, (boit p -> forall q, boit q).
  Proof.
    add_exm (forall q, boit q).
    destruct exm0.
    (* avec "P"  *)
    - exists patron.
      intro.
      assumption.
    - absurdK.
      apply H.
      intro.
      absurdK.
      apply H0.
      exists q.
      intro.
      contradiction.
  (* Comme précédemment: compléter la preuve *)

End drinkers_problem.
End classic.


 
