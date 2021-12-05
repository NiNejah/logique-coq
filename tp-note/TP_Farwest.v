Ltac forall_e H t := (generalize (H t); intro).

Require Import Setoid.

Section Farwest.
  Variable personnage: Type.
  Variables humain animal bandit cowboy: personnage -> Prop.
  Variables Averell Rantanplan Luke: personnage.
  Variable idiot: personnage -> Prop.

  Hypothesis Hh_ou_a: forall p:personnage, animal p \/ humain p.
  Hypothesis Hhna: forall p:personnage, ~(humain p /\ animal p).
  Hypothesis Hbnc: forall p:personnage, ~(cowboy p /\ bandit p).
  Hypothesis Hb: forall p:personnage, bandit p -> humain p.
  Hypothesis Hc: forall p:personnage, cowboy p -> humain p.
  Hypothesis Hhum: forall p:personnage, humain p -> cowboy p \/ bandit p.

  Hypothesis Hbni: exists p:personnage, bandit p /\ ~ idiot p.
  
  Hypothesis Hav: bandit Averell.
  Hypothesis Hlu: cowboy Luke.
  Hypothesis Hra: animal Rantanplan.
  Hypothesis Hid: idiot Rantanplan /\ idiot Averell.

  Theorem Exemple: Averell <> Luke.
  Proof.
    intro Hal.
    rewrite Hal in Hav.
    forall_e Hbnc Luke.
    apply H.
    split.
    - assumption.
    - assumption.
  Qed.

  Theorem Exercice1: ~ cowboy Rantanplan.
  Proof.
  Admitted.

  Theorem Exercice2: forall p:personnage, ~(bandit p /\ animal p).
  Proof.
  Admitted.

  Theorem Exercice3: forall p:personnage, cowboy p \/ bandit p <-> humain p.
  Proof.
  Admitted.

  Theorem Exercice4: forall p:personnage, animal p \/ cowboy p \/ bandit p.
  Proof.
  Admitted.

  Theorem Exercice5: exists p:personnage, bandit p /\ p<>Averell.
  Proof.
  Admitted.

End Farwest.
