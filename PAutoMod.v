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


(****************************************************************************)
(* 	           Bertrand Tavernier & Christine Paulin-Mohring            *)
(*                               May 2002                                   *)
(****************************************************************************)

(*i $Id$ i*)

(* The basic files for p-automata *)

Require Export Time.
Require Export TimeSyntax.
Require Export TransMod.
Require Export PAutomataMod.
Require Export Coercions.
Require Export AutoLMod.

Implicit Arguments Some [A].