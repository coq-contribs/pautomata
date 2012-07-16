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


Set Asymmetric Patterns.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import Transitions.
Require Import LList.

Section Trace_DEF.

Variable L : LTS.

Let state := LTS_State L.
Definition trace := LList state.

Variable init : state.

CoInductive exec : state -> Type :=
  | exec_init : exec init
  | exec_trans :
      forall (s s' : state) (a : LTS_Act L),
      exec s -> LTS_Trans s a s' -> exec s'. 

CoFixpoint LList_of_exec  : forall s : state, exec s -> trace :=
  fun s e =>
  match e with
  | exec_init => LNil state
  | exec_trans s s' a e' _ => LCons s' (LList_of_exec e')
  end.

CoInductive is_trace : trace -> state -> Prop :=
  | is_trace_LNil : is_trace (LNil state) init
  | is_trace_LCons :
      forall (l : trace) (s s' : state) (a : LTS_Act L),
      is_trace l s -> LTS_Trans s a s' -> is_trace (LCons s' l) s'.


End Trace_DEF.