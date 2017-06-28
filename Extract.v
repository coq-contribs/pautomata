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

Require Extraction.

Require Import PAutoMod.
Extract Constant Time => "int".   
Extract Constant T0 => "0".        
Extract Constant T1 => "1".    
Extract Constant Tmult => "( * )".
Extract Constant Tminus => "(-)".
Extract Constant Tplus => "(+)".
Extract Constant Topp => "(fun x -> -x)".
Extract Constant total_order =>
 "(fun r1 r2 -> if r1 < r2 then Coq_inleft Coq_left 
                 else if r1 = r2 then Coq_inleft Coq_right 
                 else Coq_inright)".

Recursive Extraction Library AutoLMod.
