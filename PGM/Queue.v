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
(*                       QUEUE.v                     *)
(*                     Yijia CHEN                    *)
(*                                                   *)
(*****************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Require Import Arith.
Require Import Comp.

Section QUEUE_DEF.

Variable Domain : Set.

Variable err : Domain.

Variable weight : Domain -> nat.

(**********************************************)
(* max(d1,d2) = d1 if weight(d1) > weight(d2) *)
(*            = d2 otherwise                  *)
(* so if weight(d1) == weight(d2)             *)
(*    then max(d1,d2) = d2                    *)
(**********************************************)

Let max (d1 d2 : Domain) : Domain :=
  if less (weight d2) (weight d1) then d1 else d2.

Inductive Queue : Set :=
  | empty : Queue
  | push : Domain -> Queue -> Queue.


Fixpoint queue_length (q : Queue) : nat :=
  match q with
  | empty => 0
  | push d q' => S (queue_length q')
  end.

(************************************************)
(*  pop_ele(q) = the oldest element in q        *)
(*               with minimal weight            *)
(************************************************)

Fixpoint pop_ele (q : Queue) : Domain :=
  match q with
  | empty => err
  | push d q' =>
      match q' with
      | empty => d
      | push d' p'' => max d (pop_ele q')
      end
  end.


(************************************************)
(*  pop_que(q) = q - pop_ele(q)                 *)
(************************************************)

Fixpoint pop_que (q : Queue) : Queue :=
  match q with
  | empty => empty
  | push d q' =>
      match q' with
      | empty => empty
      | push _ _ =>
          if less (weight d) (weight (pop_ele q'))
          then q'
          else push d (pop_que q')
      end
  end.

(************************************************)
(*  del_que(q,P) = q - {e | Pe}                 *)
(************************************************)

Fixpoint del_que (q1 : Queue) : Queue -> (Domain -> Prop) -> Prop :=
  match q1 with
  | empty =>
      fun q2 : Queue =>
      match q2 with
      | empty => fun P : Domain -> Prop => True
      | push d2 q2' => fun P : Domain -> Prop => False
      end
  | push d1 q1' =>
      fun (q2 : Queue) (P : Domain -> Prop) =>
      (P d1 -> del_que q1' q2 P) /\
      (~ P d1 ->
       match q2 with
       | empty => False
       | push d2 q2' => d1 = d2 /\ del_que q1' q2' P
       end)
  end.

(************************************************)
(*  push_ram(q,a) = q + a (randomly)            *)
(************************************************)

Fixpoint push_ram (q1 q2 : Queue) {struct q2} : Domain -> Prop :=
  match q1, q2 with
  | empty, empty => fun d : Domain => False
  | empty, push d2 q2' => fun d : Domain => d2 = d /\ q2' = empty
  | push d1 q1', empty => fun d : Domain => False
  | push d1 q1', push d2 q2' =>
      fun d : Domain =>
      (d2 = d -> q2' = q1) /\ (d2 <> d -> d1 = d2 /\ push_ram q1' q2' d)
  end.

End QUEUE_DEF.