Require Import Arith.

Check Nat.ltb_ge.

Check nat_ind.

Section Fibonacci_v1.
(* On veut définir le calcul de la suite de Fibonacci *)
(* u(0)=0, u(1)=1, et pour n>=2, u(n)=u(n-1)+u(n-2) *)

(* On écrit une première fonction fibo, qui traduit directement
   la relation définissant la suite *)

(* Premiere tentative échoue *)
Fail Fixpoint fibo (n:nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | S (S p) => (fibo p) + (fibo (S p))
end.
(* Le problème vient du "fibo (S p)": S p est un sous-terme de n,
   mais coq n'est pas assez malin pour le voir *)

(* Il faut "aider" coq à "voir" que S p est un sous-terme de n *)
Fixpoint fibo (n:nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | S (S p as q) => fibo p + fibo q
end.

(* Note: on aurait pu écrire essentiellement la même chose
   avec deux match imbriqués; mais c'est beaucoup moins
   lisible
Fixpoint fibo' (n:nat) : nat := 
  match n with 
  | 0 => 0
  | S q => match q with
    | 0 => 1
    | S p => fibo' p + fibo' q
    end
  end.
*)

Eval compute in (fibo 6).

(* On prouve une équation entre fibo(n+2), fibo(n) et fibo(n+1) *)
Lemma fibo_SSn: forall n, fibo (S (S n)) = fibo n + fibo (S n).
Proof.
intro n.
reflexivity.
Qed.
(* Ca servira plus tard *)
End Fibonacci_v1.

(* La fonction fibo calcule correctement, mais calcule de multiples fois
   la même chose: elle est très inefficace dans le calcul; on cherche
   généralement à réécrire le calcul de manière plus efficace.

   PROBLEME: est-on sûr que la "nouvelle" version calcule bien la même chose
   que l'"ancienne"?
*)

Section Fibonacci_v2.
(* Variante 1: on écrit une fonction avec un seul appel récursif, qui
   retourne une paire de résultats; fib2_aux n retourne (u(n),u(n+1)) *)
Fixpoint fib2_aux (n: nat): nat*nat :=
  match n with 
  | 0 => (0,1)
  | S p => let (a,b) := fib2_aux p in (b,a+b)
  end.

Eval compute in (fib2_aux 6).

(* et la fonction fib2 se contente de ne garder que le premier *)
Definition fib2 (n:nat) : nat := let (a,_) := fib2_aux n in a.

Eval compute in (fib2 6).


(* On prouve la relation entre fib2_aux et fibo *)
Lemma fib2_aux_fibo: forall n, fib2_aux n = (fibo n, fibo (S n)).
Proof.
induction n. (* P:= fun x => fib2_aux x = (fibo x, fibo (S x)) *)
Show 2.
- reflexivity.
- simpl. rewrite IHn.  auto.
Qed.

(* Normalement, il devient facile de prouver que fibo et fib2
   calculent la même chose *)
Theorem fibo_fib2: forall n, fibo n = fib2 n.
Proof.
intros n. unfold fib2. rewrite fib2_aux_fibo. reflexivity.
Qed.

(* C'était presque facile! *)
End Fibonacci_v2.

Section Fibonacci_v3.
(* Variante 2: on écrit une fonction qui généralise les deux premiers termes
   de la suite *)
(* Au lieu de 0 et 1, les deux premiers termes sont a et b *)

(* D'abord la version avec deux appels récursifs *)
Fixpoint fibo_gen (a b n: nat) : nat :=
  match n with
  | 0 => a
  | 1 => b
  | S (S p as q) => fibo_gen a b p + fibo_gen a b q
end.

(* Comme pour fibo: équation entre fibo_gen(n+2), fibo_gen(n) et fibo_gen(n+1) *)
Lemma fibo_gen_SSn: forall n a b, 
   fibo_gen a b (S (S n)) = fibo_gen a b n + fibo_gen a b (S n).
Proof.
reflexivity.
Qed.

(* Première chose: avec a=0 et b=1, on retrouve fibo *)
Lemma fibo_gen_fibo: forall n, fibo_gen 0 1 n = fibo n.
Proof.
induction n.
- simpl. reflexivity.
- simpl. rewrite IHn.
(* Malheur! IHn ne parle que de n, on a besoin de réécrire aussi pour p... *)
Abort.

(* On réécrit le lemme, avec à la fois n et (S n) *)
Lemma fibo_gen_fibo: forall n, 
  fibo_gen 0 1 n = fibo n /\ fibo_gen 0 1 (S n) = fibo (S n).
Proof.
induction n.
- simpl. split; reflexivity.
- destruct IHn as [IHn1 IHn2].
  split.
  + assumption.
  + rewrite fibo_SSn. rewrite fibo_gen_SSn. rewrite IHn1. rewrite IHn2. reflexivity.
Qed.

(* La fonction généralisée, permet d'écrire une fonction simplement récursive *)
(* L'appel récursif se fait sur d'autres valeurs initiales *)
Fixpoint fibo_gen_bis (a b n:nat) : nat :=
  match n with
  | 0 => a
  | S p => fibo_gen_bis b (a+b) p
end.
(* C'est nouveau par rapport à la version initiale *)

Eval compute in fibo_gen 0 1 10.
Eval compute in fibo_gen_bis 0 1 10.
(* Ce serait bien de prouver que ces deux fonctions retournent la même chose *)

(* La version qui retourne un couple de valeurs, version fibo_gen *)
Fixpoint fibo_gen_aux (a b n:nat) : nat*nat :=
  match n with 
  | 0 => (a,b)
  | S p => let (a',b'):= fibo_gen_aux a b p in (b',a'+b')
  end.

(* La version qui retourne un couple de valeurs, version fibo_gen_bis *)
Fixpoint fibo_gen_bis_aux (a b n:nat) : nat * nat :=
  match n with
  | 0 => (a,b)
  | S p => fibo_gen_bis_aux b (a+b) p
  end.

Lemma fibogen_aux_prop: forall a b n, fibo_gen_aux a b n = fibo_gen_bis_aux a b n.
Proof.
intros a b n. generalize a b. induction n.
- reflexivity.
- intros aa bb. simpl. rewrite <- IHn.
(* On voit apparaître un but qui ne concerne plus que fibo_gen_aux; on va annuler
   la preuve en cours et passer à un lemme sur fibo_gen_aux. *)
Abort.

(* On écrit un lemme sur fibo_gen_aux *)
Lemma fibogen_prop: forall a b n, fibo_gen_aux a b (S n) = fibo_gen_aux b (a+b) n.
Proof.
intros a b n; generalize a b; induction n.
- reflexivity.
- intros aa bb. simpl. rewrite <- IHn. simpl. reflexivity.
Qed.

(* Avec ce lemme, on peut reprendre la preuve abandonnée *)
Lemma fibogen_aux_prop: forall a b n, fibo_gen_aux a b n = fibo_gen_bis_aux a b n.
Proof.
intros a b n; generalize a b; induction n; try reflexivity.
intros aa bb. simpl. rewrite <- IHn.
apply fibogen_prop.
Qed.

Lemma fibo_gen_aux_naux: forall a b n, 
  fibo_gen_aux a b n = (fibo_gen a b n, fibo_gen a b (S n)).
Proof.
intros a b n. induction n.
- simpl. reflexivity.
- rewrite fibo_gen_SSn. simpl. rewrite IHn. reflexivity.
Qed.

Lemma fibo_gen_bis_aux_naux: forall a b n,
  fibo_gen_bis_aux a b n = (fibo_gen_bis a b n, fibo_gen_bis a b (S n)).
Proof.
intros a b n; generalize a b; induction n.
- intros a' b'. simpl. reflexivity.
- intros a' b'. simpl. rewrite IHn. reflexivity.
Qed.

Theorem fibo_generalise: forall a b n, fibo_gen a b n = fibo_gen_bis a b n.
Proof.
intros a b n.
replace (fibo_gen a b n) with (fst (fibo_gen_aux a b n)).
replace (fibo_gen_bis a b n) with (fst (fibo_gen_bis_aux a b n)).
- f_equal; apply fibogen_aux_prop.
- rewrite fibo_gen_bis_aux_naux. reflexivity.
- rewrite fibo_gen_aux_naux; reflexivity.
Qed.

Theorem fibogen_bis_fibo: forall n, fibo_gen_bis 0 1 n = fibo n.
Proof.
intro n.
rewrite <- fibo_generalise.
apply fibo_gen_fibo.
Qed.

End Fibonacci_v3.

(* Les deux fonctions generalisées "bis" sont des variantes de l'itération
   d'une fonction; on peut montrer un théorème un peu général: il y a deux
   façons de définir l'itération n fois d'une fonction, et elles sont
   équivalentes *)

Section Iteration.
  Variable A: Type.
  Variable f: A->A.

  Fixpoint iterate1 n (x:A) : A :=
  match n with
  | 0 => x
  | S p => iterate1 p (f x)
  end.

  Fixpoint iterate2 n (x:A) : A :=
  match n with
  | 0 => x
  | S p => f (iterate2 p x)
  end.

  (* But: montrer que iterate1 et iterate2 calculent la même chose *)

  Lemma iter1: forall n x, iterate1 n (f x) = f (iterate1 n x).
  Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. intro x. rewrite IHn. reflexivity.
  Qed.

  Lemma iter2: forall n x, iterate2 n (f x) = f (iterate2 n x).
  Proof.
  induction n.
  - simpl; reflexivity.
  - intro x. simpl. rewrite IHn. reflexivity.
  Qed.

  Theorem iter: forall n x, iterate1 n x = iterate2 n x.
  Proof.
  induction n.
  - intros x; reflexivity.
  - intros x. simpl. rewrite IHn. apply iter2.
  Qed.
End Iteration.

Check iter.