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
  Definition du p-automate Bus
*********************************************************************)
Require Import Contexte.
Import AutoLGen.

Inductive loc : Set :=
  | Idle : loc
  | Active : loc
  | Collision : loc.
Inductive act : Set :=
  | begin : act
  | fin : act
  | CD : act
  | busy : act.

Module localize_struct.
Definition local (v : VarName) : Prop :=
  match v with
  | Bus_y => True
  | _ => False
  end.
End localize_struct.

Module AutoL. (* AutoL_struct *)
Module L := Localize localize_struct.

Definition yname := Local (L.mkVarLoc Bus_y I).

Definition Vars : Set := VectVar L.TV.

Definition Loc := loc.

Definition Act := act.

Definition init := Idle.

Section Invariants.

Variable l : loc.
Variable S : Time.
Variable v : Vars.

Let Inva0 : P_Invariant Vars loc := fun l S v => let y := v yname in True.

Let Inva1 : P_Invariant Vars loc := fun l S v => let y := v yname in True.

Let Inva2 : P_Invariant Vars loc := fun l S v => let y := v yname in False.

Definition Inv l S v :=
  match l with
  | Idle => Inva0 l S v
  | Active => Inva1 l S v
  | Collision => Inva2 l S v
  end.

End Invariants.

Section Updates.

Inductive trans1_1 (S : Time) (v1 v2 : Vars) : act -> loc -> loc -> Prop :=
    cons_trans1_1 :
      let y' := v2 yname in
      let y := v1 yname in
      True -> y' = S :>Time -> y' = y -> trans1_1 S v1 v2 begin Idle Active.

Inductive trans1_2 (S : Time) (v1 v2 : Vars) : act -> loc -> loc -> Prop :=
    cons_trans1_2 :
      let y' := v2 yname in
      let y := v1 yname in
      True -> y' = S :>Time -> y' = y -> trans1_2 S v1 v2 fin Active Idle.

Inductive trans1_3 (S : Time) (v1 v2 : Vars) : act -> loc -> loc -> Prop :=
    cons_trans1_3 :
      let y' := v2 yname in
      let y := v1 yname in
      S -/ y </ Sig ->
      y' = S :>Time -> y' = y -> trans1_3 S v1 v2 begin Active Collision.

Inductive trans1_4 (S : Time) (v1 v2 : Vars) : act -> loc -> loc -> Prop :=
    cons_trans1_4 :
      let y' := v2 yname in
      let y := v1 yname in
      True -> y' = y -> trans1_4 S v1 v2 CD Collision Idle.

Inductive trans1_5 (S : Time) (v1 v2 : Vars) : act -> loc -> loc -> Prop :=
    cons_trans1_5 :
      let y' := v2 yname in
      let y := v1 yname in
      S -/ y >=/ Sig -> y' = y -> trans1_5 S v1 v2 busy Active Active.


Inductive trans (a : act) (S : Time) (l1 : loc) (v1 : Vars) 
(l2 : loc) (v2 : Vars) : Prop :=
  | cas_trans1_1 : trans1_1 S v1 v2 a l1 l2 -> trans a S l1 v1 l2 v2
  | cas_trans1_2 : trans1_2 S v1 v2 a l1 l2 -> trans a S l1 v1 l2 v2
  | cas_trans1_3 : trans1_3 S v1 v2 a l1 l2 -> trans a S l1 v1 l2 v2
  | cas_trans1_4 : trans1_4 S v1 v2 a l1 l2 -> trans a S l1 v1 l2 v2
  | cas_trans1_5 : trans1_5 S v1 v2 a l1 l2 -> trans a S l1 v1 l2 v2.

Definition Trans := trans.
End Updates.
End AutoL.

Definition bus : PautL := mk_autol (mk_auto AutoL.Inv AutoL.Trans).

Definition y : Loc bus := AutoL.L.mkVarLoc Bus_y I.

