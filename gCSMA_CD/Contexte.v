(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


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

