(****************************************************************************)
(* 	           Emmanuel Freund & Christine Paulin-Mohring               *)
(*                               July 1st 2000                              *)
(****************************************************************************)
(*i $Id$ i*)

(*********************************************************)
(*           Modelisation de l'ABR                       *)
(*********************************************************)


Require Import PAuto.

Section ABR_Model.

(* Les paramètres : tau, le moment de l'observation, tau2 et tau3 les delais 
   minimaux et maximaux de transmissions *)

Variable tau tau2 tau3 : Time.

(* L'automate P1 (Aenv) qui représente l'arrivée des cellules RM et 
   le snapshot a l'instant tau *)
(* Une seule variable R correspondant à la valeur de la cellule RM *)

Definition ABRvar1 : Set := Z.
Inductive ABRloc1 : Set :=
  | Wait : ABRloc1
  | EndE : ABRloc1.
Inductive ABRact1 : Set :=
  | snapshot1 : ABRact1
  | newRm1 : ABRact1.

Inductive ABRtrans1 : P_Transitions ABRvar1 ABRloc1 ABRact1 :=
  | trans1_1 : forall R : ABRvar1, ABRtrans1 snapshot1 tau Wait R EndE R
  | trans1_2 :
      forall (R R' : ABRvar1) (s : Time),
      (R' > 0)%Z -> ABRtrans1 newRm1 s Wait R Wait R'.

Definition ABRinv1 : P_Invariant ABRvar1 ABRloc1 :=
  fun l s r => match l with
               | Wait => s <=/ tau
               | EndE => True
               end.

Definition P1 : p_auto ABRvar1 := Build_p_auto ABRinv1 ABRtrans1.

(* Modelisation de l'automate AI qui  représente l'algorithme idéal       *)
(* Les variables sont de la forme (E,R) avec R la valeur de la cellule 
   RM et E la valeur ideale calculée                                      *)

Definition ABRvar2 : Set := (Z * Z)%type.
Inductive ABRloc2 : Set :=
  | UpdE : ABRloc2
  | Idle : ABRloc2
  | EndI : ABRloc2.
Inductive ABRact2 : Set :=
  | newRm2 : ABRact2
  | I1 : ABRact2
  | I2a : ABRact2
  | I2b : ABRact2
  | I3 : ABRact2
  | snapshot2 : ABRact2.

Inductive ABRtrans2 : P_Transitions ABRvar2 ABRloc2 ABRact2 :=
  | trans2_1 : forall v : ABRvar2, ABRtrans2 snapshot2 tau Idle v EndI v
  | trans2_2 :
      forall (R E R' : Z) (s : Time),
      (R' > 0)%Z -> ABRtrans2 newRm2 s Idle (E, R) UpdE (E, R')
  | trans2_3 :
      forall (R E : Z) (s : Time),
      s +/ tau3 </ tau ->
      tau </ s +/ tau2 ->
      (R > E)%Z -> ABRtrans2 I2a s UpdE (E, R) Idle (R, R)
  | trans2_4 :
      forall (R E : Z) (s : Time),
      s +/ tau3 <=/ tau ->
      tau </ s +/ tau2 ->
      (R <= E)%Z -> ABRtrans2 I2b s UpdE (E, R) Idle (E, R)
  | trans2_5 :
      forall (v : ABRvar2) (s : Time),
      tau </ s +/ tau3 -> ABRtrans2 I3 s UpdE v Idle v
  | trans2_6 :
      forall (R E : Z) (s : Time),
      s +/ tau2 <=/ tau -> ABRtrans2 I1 s UpdE (E, R) Idle (R, R).

Definition ABRinv2 : P_Invariant ABRvar2 ABRloc2 :=
  fun l s r => match l with
               | UpdE => False
               | _ => True
               end.

Definition P2 : p_auto ABRvar2 := Build_p_auto ABRinv2 ABRtrans2.          


(* Modélisation de l'automate qui représente l'algorithme approximatif B' *)

(* Cet automate a pour variables (Emx,Efi,Ela,R,A,tfi,tla) 
   Efi et Ela sont les deux valeurs stockées de débit correspondant 
   au temps tfi et tla, 
   Emx est une variable auxiliaire qui stocke la valeur max de Ela et Efi
   A représente la valeur de débit courante et 
   R la valeur de la dernière cellule reçue
  *)

Record ABRvar3 : Set := cons_ABRvar3
  {Emx : Z; Efi : Z; Ela : Z; R : Z; A : Z; tfi : Time; tla : Time}.

Inductive ABRloc3 : Set :=
  | UpdAG : ABRloc3
  | Less : ABRloc3
  | Greater : ABRloc3
  | UpdAL : ABRloc3
  | EndB : ABRloc3.

Inductive ABRact3 : Set :=
  | newRm3 : ABRact3
  | empty3 : ABRact3
  | snapshot3 : ABRact3.

Inductive ABRtrans3 : P_Transitions ABRvar3 ABRloc3 ABRact3 :=
  | trans3_1 : forall v : ABRvar3, ABRtrans3 snapshot3 tau Greater v EndB v
  | trans3_2 :
      forall (s : Time) (v : ABRvar3),
      s </ tfi v -> ABRtrans3 snapshot3 tau Less v EndB v
  | trans3_3 :
      forall (s : Time) (v : ABRvar3) (R' : Z),
      (R' > 0)%Z ->
      ABRtrans3 newRm3 s Greater v UpdAG
        (cons_ABRvar3 (Emx v) (Efi v) (Ela v) R' (A v) (tfi v) (tla v))
  | trans3_4 :
      forall (s : Time) (v : ABRvar3) (R' : Z),
      (R' > 0)%Z ->
      s </ tfi v ->
      ABRtrans3 newRm3 s Less v UpdAL
        (cons_ABRvar3 (Emx v) (Efi v) (Ela v) R' (A v) (tfi v) (tla v))
  | trans3_5 :
      forall (s : Time) (v : ABRvar3) (r' : Z),
      s </ tfi v ->
      (Emx v <= R v)%Z ->
      tfi v </ s +/ tau3 ->
      s +/ tau3 </ tla v ->
      ABRtrans3 empty3 s UpdAL v Less
        (cons_ABRvar3 (R v) (Efi v) (R v) (R v) (A v) (tfi v) (s +/ tau3))
  | trans3_6 :
      forall (s : Time) (v : ABRvar3),
      s </ tfi v ->
      (Emx v <= R v)%Z ->
      tfi v </ s +/ tau3 ->
      tfi v = tla v ->
      ABRtrans3 empty3 s UpdAL v Less
        (cons_ABRvar3 (R v) (Efi v) (R v) (R v) (A v) (tfi v) (s +/ tau3))
  | trans3_7 :
      forall (s : Time) (v : ABRvar3),
      s </ tfi v ->
      (Emx v <= R v)%Z ->
      tfi v </ tla v ->
      tla v </ s +/ tau3 ->
      ABRtrans3 empty3 s UpdAL v Less
        (cons_ABRvar3 (R v) (Efi v) (R v) (R v) (A v) (tfi v) (tla v))
  | trans3_8 :
      forall (s : Time) (v : ABRvar3),
      s </ tfi v ->
      (Emx v <= R v)%Z ->
      s +/ tau3 </ tfi v ->
      (A v <= R v)%Z ->
      ABRtrans3 empty3 s UpdAL v Less
        (cons_ABRvar3 (R v) (R v) (R v) (R v) (A v) (s +/ tau3) (s +/ tau3))
  | trans3_9 :
      forall (s : Time) (v : ABRvar3),
      s </ tfi v ->
      (Emx v <= R v)%Z ->
      s +/ tau3 </ tfi v ->
      (A v > R v)%Z ->
      ABRtrans3 empty3 s UpdAL v Less
        (cons_ABRvar3 (R v) (R v) (R v) (R v) (A v) (tfi v) (tfi v))
  | trans3_10 :
      forall (s : Time) (v : ABRvar3),
      s </ tfi v ->
      (Emx v > R v)%Z ->
      (R v < Ela v)%Z ->
      ABRtrans3 empty3 s UpdAL v Less
        (cons_ABRvar3 (Emx v) (Emx v) (R v) (R v) (A v) (tfi v) (s +/ tau2))
  | trans3_11 :
      forall (s : Time) (v : ABRvar3),
      s </ tfi v ->
      (Emx v > R v)%Z ->
      (Ela v <= R v)%Z ->
      ABRtrans3 empty3 s UpdAL v Less
        (cons_ABRvar3 (Emx v) (Emx v) (R v) (R v) (A v) (tfi v) (tla v))
  | trans3_12 :
      forall (s : Time) (v : ABRvar3),
      tfi v <=/ s ->
      (A v <= R v)%Z ->
      ABRtrans3 empty3 s UpdAG v Less
        (cons_ABRvar3 (R v) (R v) (R v) (R v) (A v) (s +/ tau3) (s +/ tau3))
  | trans3_13 :
      forall (s : Time) (v : ABRvar3),
      tfi v <=/ s ->
      (A v > R v)%Z ->
      ABRtrans3 empty3 s UpdAG v Less
        (cons_ABRvar3 (R v) (R v) (R v) (R v) (A v) (s +/ tau2) (s +/ tau2))
  | trans3_14 :
      forall (s : Time) (v : ABRvar3),
      tfi v = s ->
      tla v = s ->
      ABRtrans3 empty3 s Less v Greater
        (cons_ABRvar3 (Ela v) (Ela v) (Ela v) (R v) (Efi v) (tla v) (tla v))
  | trans3_15 :
      forall (s : Time) (v : ABRvar3),
      tfi v = s ->
      s </ tla v ->
      ABRtrans3 empty3 s Less v Greater
        (cons_ABRvar3 (Ela v) (Ela v) (Ela v) (R v) (Efi v) (tla v) (tla v)).
	
Definition ABRinv3 : P_Invariant ABRvar3 ABRloc3 :=
  fun l s v =>
  match l with
  | Less => s </ tfi v
  | UpdAL => False
  | UpdAG => False
  | _ => True
  end.

Definition P3 : p_auto ABRvar3 := Build_p_auto ABRinv3 ABRtrans3.

(*  La synchronisation des trois automates *)

(* Ensemble d'index à trois éléments *)
Inductive I : Set :=
  | one : I
  | two : I
  | three : I.

(* On construit une fonction de type (i:I)(P i) à partir de 3 valeurs *)
Definition triple (P : I -> Type) (p1 : P one) (p2 : P two) 
  (p3 : P three) (i : I) : P i :=
  match i as x return (P x) with
  | one => p1
  | two => p2
  | three => p3
  end.

(* Famille des types de variables *)
Definition ABVRSync_I : I -> Set :=
  triple (fun i : I => Set) ABRvar1 ABRvar2 ABRvar3.

(* Famille des automates *)
Definition ABRaut_I : forall i : I, p_auto (ABVRSync_I i) :=
  triple (fun i : I => p_auto (ABVRSync_I i)) P1 P2 P3.

(* Le type des actions *)
Definition ABRactI (i : I) : Set := option (P_Act (ABRaut_I i)).

Definition ABRact : Set := forall i : I, ABRactI i.

(* Le type des variables de l'automate synchronisé :
   La variable R est commune aux trois automates *)
Record ABVRSync : Set :=  {E : Z; p3 : ABRvar3}.

(* La fonction de projection indexée *)
Definition ABRproj (i : I) (V : ABVRSync) : ABVRSync_I i :=
  triple ABVRSync_I (R (p3 V)) (E V, R (p3 V)) (p3 V) i.

(* Le vecteur de synchronisation *)
Definition sync1 : ABRact :=
  triple ABRactI (Some newRm1) (Some newRm2) (Some newRm3).
Definition sync2 : ABRact :=
  triple ABRactI (Some snapshot1) (Some snapshot2) (Some snapshot3).

Inductive ABR_vectSync : ABRact -> Prop :=
  | ABR_sync1 : ABR_vectSync sync1
  | ABR_sync2 : ABR_vectSync sync2.

(* Definition de l'automate synchronisé *)
Definition P_ABR := Pauto_sync_mult ABRproj ABR_vectSync.

End ABR_Model.


