(********************************************************************
  Fichier gCSMA_CD.v		
  Modelisation du p-automate definit sous l'IHM vers COQ                      
  Projet Calife 2001                              
********************************************************************


********************************************************************
  Modelisation du systeme gCSMA_CD          
  Fichier Contexte.v
********************************************************************)

Require Export Arith.
Require Export ZArith.
Require Export List.
Require Export Peano_dec.
Require Export PAutoMod.


(********************************************************************
  Definition de l'environnement global
*********************************************************************)
Parameter Sig : Time.
Parameter Lambda : Time.
Parameter n : nat.

Inductive VarName : Set :=
  | Sender_x : VarName
  | Bus_y : VarName.

Definition TypeVarName (n : VarName) :=
  match n return Set with
  | Sender_x => Time
  | Bus_y => Time
  end.

Module Globals.
Definition V := VarName.
Definition TV := TypeVarName.
End Globals.

Module AutoLGen := AutoL_general Globals.

