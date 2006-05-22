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
  Definition du p-automate Sender
*********************************************************************)

Require Import Contexte.
Import AutoLGen.

Variable _pid : Z.

Inductive loc : Set :=
  | Wait : loc
  | Transmit : loc
  | Retry : loc.
Inductive act : Set :=
  | CD : act
  | begin : act
  | busy : act
  | fin : act.

Module localize_struct.
Definition local (v : VarName) : Prop :=
  match v with
  | Sender_x => True
  | _ => False
  end.
End localize_struct.

Module AutoL. (* : AutoL_struct. *)
Module L := Localize localize_struct.

Definition xname := Local (L.mkVarLoc Sender_x I).

Definition Vars : Set := VectVar L.TV.

Definition Loc := loc.

Definition Act := act.

Definition init := Wait.

Section Invariants.

Variable l : loc.
Variable S : Time.
Variable v : Vars.

Let Inva0 : P_Invariant Vars loc := fun l S v => let x := v xname in True.

Let Inva1 : P_Invariant Vars loc :=
  fun l S v => let x := v xname in S -/ x <=/ Lambda.

Let Inva2 : P_Invariant Vars loc :=
  fun l S v => let x := v xname in S -/ x <=/ 2 */ Sig.

Definition Inv l S v :=
  match l with
  | Wait => Inva0 l S v
  | Transmit => Inva1 l S v
  | Retry => Inva2 l S v
  end.

End Invariants.

Section Updates.

Inductive trans1_1 (S : Time) (v1 v2 : Vars) : act -> loc -> loc -> Prop :=
    cons_trans1_1 :
      let x' := v2 xname in
      let x := v1 xname in
      True -> x' = S :>Time -> x' = x -> trans1_1 S v1 v2 CD Wait Wait.

Inductive trans1_2 (S : Time) (v1 v2 : Vars) : act -> loc -> loc -> Prop :=
    cons_trans1_2 :
      let x' := v2 xname in
      let x := v1 xname in
      True -> x' = S :>Time -> x' = x -> trans1_2 S v1 v2 begin Wait Transmit.

Inductive trans1_3 (S : Time) (v1 v2 : Vars) : act -> loc -> loc -> Prop :=
    cons_trans1_3 :
      let x' := v2 xname in
      let x := v1 xname in
      S -/ x </ Sig ->
      x' = S :>Time -> x' = x -> trans1_3 S v1 v2 CD Transmit Retry.

Inductive trans1_4 (S : Time) (v1 v2 : Vars) : act -> loc -> loc -> Prop :=
    cons_trans1_4 :
      let x' := v2 xname in
      let x := v1 xname in
      S -/ x <=/ 2 */ Sig ->
      x' = S :>Time -> x' = x -> trans1_4 S v1 v2 begin Retry Transmit.

Inductive trans1_5 (S : Time) (v1 v2 : Vars) : act -> loc -> loc -> Prop :=
    cons_trans1_5 :
      let x' := v2 xname in
      let x := v1 xname in
      True -> x' = S :>Time -> x' = x -> trans1_5 S v1 v2 busy Wait Retry.

Inductive trans1_6 (S : Time) (v1 v2 : Vars) : act -> loc -> loc -> Prop :=
    cons_trans1_6 :
      let x' := v2 xname in
      let x := v1 xname in
      True -> x' = S :>Time -> x' = x -> trans1_6 S v1 v2 CD Wait Retry.

Inductive trans1_7 (S : Time) (v1 v2 : Vars) : act -> loc -> loc -> Prop :=
    cons_trans1_7 :
      let x' := v2 xname in
      let x := v1 xname in
      S -/ x <=/ 2 */ Sig ->
      x' = S :>Time -> x' = x -> trans1_7 S v1 v2 CD Retry Retry.

Inductive trans1_8 (S : Time) (v1 v2 : Vars) : act -> loc -> loc -> Prop :=
    cons_trans1_8 :
      let x' := v2 xname in
      let x := v1 xname in
      S -/ x <=/ 2 */ Sig ->
      x' = S :>Time -> x' = x -> trans1_8 S v1 v2 busy Retry Retry.

Inductive trans1_9 (S : Time) (v1 v2 : Vars) : act -> loc -> loc -> Prop :=
    cons_trans1_9 :
      let x' := v2 xname in
      let x := v1 xname in
      True -> x' = x -> trans1_9 S v1 v2 busy Transmit Transmit.

Inductive trans1_10 (S : Time) (v1 v2 : Vars) : act -> loc -> loc -> Prop :=
    cons_trans1_10 :
      let x' := v2 xname in
      let x := v1 xname in
      S -/ x = Lambda :>Time ->
      x' = S :>Time -> x' = x -> trans1_10 S v1 v2 fin Transmit Wait.



Inductive trans (a : act) (S : Time) (l1 : loc) (v1 : Vars) 
(l2 : loc) (v2 : Vars) : Prop :=
  | cas_trans1_1 : trans1_1 S v1 v2 a l1 l2 -> trans a S l1 v1 l2 v2
  | cas_trans1_2 : trans1_2 S v1 v2 a l1 l2 -> trans a S l1 v1 l2 v2
  | cas_trans1_3 : trans1_3 S v1 v2 a l1 l2 -> trans a S l1 v1 l2 v2
  | cas_trans1_4 : trans1_4 S v1 v2 a l1 l2 -> trans a S l1 v1 l2 v2
  | cas_trans1_5 : trans1_5 S v1 v2 a l1 l2 -> trans a S l1 v1 l2 v2
  | cas_trans1_6 : trans1_6 S v1 v2 a l1 l2 -> trans a S l1 v1 l2 v2
  | cas_trans1_7 : trans1_7 S v1 v2 a l1 l2 -> trans a S l1 v1 l2 v2
  | cas_trans1_8 : trans1_8 S v1 v2 a l1 l2 -> trans a S l1 v1 l2 v2
  | cas_trans1_9 : trans1_9 S v1 v2 a l1 l2 -> trans a S l1 v1 l2 v2
  | cas_trans1_10 : trans1_10 S v1 v2 a l1 l2 -> trans a S l1 v1 l2 v2.

Definition Trans := trans.

End Updates.
End AutoL.

Definition sender : PautL := mk_autol (mk_auto AutoL.Inv AutoL.Trans).

Definition x : Loc sender := AutoL.L.mkVarLoc Sender_x I.

