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
(*                      String.v                     *)
(*                     Yijia CHEN                    *)
(*                                                   *)
(*****************************************************)

Require Import List.
Require Import Bool.

Set Implicit Arguments.
Unset Strict Implicit.

Section LETTER_DEF.

Inductive letter : Set :=
  | A : letter
  | B : letter
  | C : letter
  | D : letter
  | E : letter
  | F : letter
  | G : letter
  | H : letter
  | I : letter
  | J : letter
  | K : letter
  | L : letter
  | M : letter
  | N : letter
      (* | O : letter, reserved for 0 for nat *)
  | P : letter
  | Q : letter
  | R : letter
      (* | S : letter, reserved for successor of nat *)
  | T : letter
  | U : letter
  | V : letter
  | W : letter
  | X : letter
  | Y : letter
  | Z : letter.

Definition eq_letter (l1 l2 : letter) : bool :=
  match l1, l2 with
  | A, A => true
  | B, B => true
  | C, C => true
  | D, D => true
  | E, E => true
  | F, F => true
  | G, G => true
  | H, H => true
  | I, I => true
  | J, J => true
  | K, K => true
  | L, L => true
  | M, M => true
  | LETTER_DEF.N, LETTER_DEF.N => true
      (*                  | O O => true *)
  | P, P => true
  | Q, Q => true
  | R, R => true
      (*                  | S S => true *)
  | T, T => true
  | U, U => true
  | V, V => true
  | W, W => true
  | X, X => true
  | Y, Y => true
  | Z, Z => true
  | _, _ => false
  end.

End LETTER_DEF.

Section STRING_DEF.

Definition string := list letter.

Definition voidstring : string := nil.

Fixpoint eq_string (str1 str2 : string) {struct str2} : bool :=
  match str1, str2 with
  | nil, nil => true
  | l1 :: str11, l2 :: str21 =>
      if eq_letter l1 l2 then eq_string str11 str21 else false
  | _, _ => false
  end.

Fixpoint prefix_string (target prefix : string) {struct prefix} : bool :=
  match target, prefix with
  | nil, nil => true
  | l1 :: str1, l2 :: str2 =>
      if eq_letter l1 l2 then prefix_string str1 str2 else false
  | _, _ => false
  end.

Fixpoint extract_string (target prefix : string) {struct prefix} : string :=
  match target, prefix with
  | _, nil => target
  | l1 :: str1, l2 :: str2 =>
      if eq_letter l1 l2 then extract_string str1 str2 else voidstring
  | nil, l2 :: str2 => voidstring
  end.

End STRING_DEF.