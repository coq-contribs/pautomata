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


(*****************************************************)
(*                       COMP.v                      *)
(*                     Yijia CHEN                    *)
(*                                                   *)
(*****************************************************)

Require Import Bool.

Section COMPARE_DEF.

Fixpoint less (n1 : nat) : nat -> bool :=
  match n1 with
  | O => fun n2 : nat => match n2 with
                         | O => false
                         | S n2' => true
                         end
  | S n1' =>
      fun n2 : nat => match n2 with
                      | O => false
                      | S n2' => less n1' n2'
                      end
  end.

End COMPARE_DEF.