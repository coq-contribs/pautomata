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


(** Generalised automata associated to a p-automata *)

Require Export PAutomataMod.
Require Export GAutomata.
Require Export TimeSyntax.

Module Gauto_of (P: Pauto_struct) <: Gauto_struct.
Definition Loc := P.Loc.
Definition Act := P.Act.

Record gVar : Type := {time_of : Time; val_of : P.Var}.
Definition Var:=gVar.

Definition Evo : G_Evolution Var Loc := 
   fun l v w => time_of v </ time_of w 
   /\ val_of v = val_of w
   /\ forall T : Time, time_of v </ T -> T <=/ time_of w -> P.Inv l T (val_of v).
  
Definition Trans : G_Transitions Var Loc Act := 
   fun a l v l' w => time_of v = time_of w 
   /\ P.Trans a (time_of v) l (val_of v) l' (val_of w).

End Gauto_of.
