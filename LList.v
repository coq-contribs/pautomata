(****************************************************************)
(*                               LList.v                        *)
(****************************************************************)
(*i 	$Id$ i*)

Section LLIST.

Set Implicit Arguments.
Unset Strict Implicit.
Variable A : Type.
Variable default : A.

(***** Definition des LLists, listes finies ou infinies *****)

CoInductive LList : Type :=
  | LNil : LList
  | LCons : A -> LList -> LList. 

(* Egalité entre 2 LList, définie co-inductivement *)

CoInductive eq_LList : LList -> LList -> Prop :=
  | eq_LNil : eq_LList LNil LNil
  | eq_LCons :
      forall (a : A) (l l' : LList),
      eq_LList l l' -> eq_LList (LCons a l) (LCons a l').

Lemma eq_LList_refl : forall l : LList, eq_LList l l.
cofix.
simple destruct l.
constructor.
constructor; trivial.
Qed.

Lemma eq_LList_sym : forall l l' : LList, eq_LList l l' -> eq_LList l' l.
cofix.
simple destruct 1.
constructor.
constructor.
apply eq_LList_sym; trivial.
Qed.


Lemma eq_LList_trans :
 forall l1 l2 l3 : LList, eq_LList l1 l2 -> eq_LList l2 l3 -> eq_LList l1 l3.

cofix.
simple destruct 1; intros; trivial.
inversion_clear H1.
constructor.
apply eq_LList_trans with l'; trivial.
Qed.

(***** fini ou infini *****)

Inductive finite : LList -> Prop :=
  | vide : finite LNil
  | plusun : forall (l : LList) (a : A), finite l -> finite (LCons a l).

CoInductive infinite : LList -> Prop :=
    plus : forall (l : LList) (a : A), infinite l -> infinite (LCons a l).

Lemma finite_not_infinite : forall l : LList, finite l -> infinite l -> False.
simple induction 1.
intro Inf; inversion_clear Inf.
intros.
inversion_clear H2.
auto.
Qed.

(***** Verification de la presence d'un element dans la liste *****)

Inductive members (a : A) : LList -> Prop :=
  | hd_members : forall l : LList, members a (LCons a l)
  | tl_members :
      forall (l : LList) (b : A), members a l -> members a (LCons b l). 

(***** Longueur d'une LList *****)

Inductive lt_length : nat -> LList -> Prop :=
  | lt_length_O : forall (b : A) (l : LList), lt_length 0 (LCons b l)
  | lt_length_S :
      forall (n : nat) (b : A) (l : LList),
      lt_length n l -> lt_length (S n) (LCons b l).

Inductive le_length : nat -> LList -> Prop :=
  | le_length_0 : forall l : LList, le_length 0 l
  | le_length_S :
      forall (n : nat) (b : A) (l : LList),
      le_length n l -> le_length (S n) (LCons b l).

Lemma le_length_1 : forall (b : A) (l : LList), le_length 1 (LCons b l).
intros; apply le_length_S; constructor.
Qed.

Lemma ltlength_lelength :
 forall (n : nat) (l : LList), lt_length n l -> le_length n l.
simple induction 1; constructor; trivial.
Qed.

Lemma lelength_ltlength :
 forall (n : nat) (l : LList), le_length (S n) l -> lt_length n l.
simple induction n; intros.
inversion_clear H.
constructor.
inversion_clear H0.
constructor; auto.
Qed.


Lemma inf_lt_length :
 forall (n : nat) (l : LList), infinite l -> lt_length n l.
simple induction n.
simple destruct 1; constructor.
simple destruct 2; constructor; auto.
Qed.

(**** Concaténation  *****)

(* ConcatL m l concatene l a la tete de m 
   si l = l1.l2.....ln.nil alors ConcatL m l = l1.l2.....ln.m
   si l est infini alors ConcatL m l se comporte comme l 
*)

CoFixpoint ConcatL  : LList -> LList -> LList :=
  fun m l : LList =>
  match l with
  | LNil => m
  | LCons a l' => LCons a (ConcatL m l')
  end.

Fixpoint Lnth_tl (n : nat) : LList -> LList :=
  fun l =>
  match n, l with
  | O, l => l
  | S m, LNil => LNil
  | S m, LCons a l' => Lnth_tl m l'
  end.
 
(* renvoie le premier element d'une liste non vide, et la valeur par defaut 
   default pour une liste vide *)

Definition FirstA (l : LList) : A :=
  match l with
  | LNil => default
  | LCons a _ => a
  end.

(* renvoie le n-eme element de la liste, sachant que le premier element est 
   indice par 0, renvoie default si la liste a moins de n+1 elements
*)

Fixpoint Lnth (n : nat) : LList -> A :=
  fun l =>
  match n, l with
  | O, LCons a _ => a
  | S m, LCons _ l' => Lnth m l'
  | n, LNil => default
  end. 


Inductive eq_until : nat -> LList -> LList -> Prop :=
  | eq_until_O : forall l l' : LList, eq_until 0 l l'
  | eq_until_S :
      forall (n : nat) (b : A) (l l' : LList),
      eq_until n l l' -> eq_until (S n) (LCons b l) (LCons b l').


End LLIST.

