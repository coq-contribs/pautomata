
(*****************************************************)
(*                       Map.v                       *)
(*                     Yijia CHEN                    *)
(*                                                   *)
(*****************************************************)

Require Import Bool.
Require Import List.

Set Implicit Arguments.
Unset Strict Implicit.

Section MAP_DEF.

Variable Domain : Set.

Variable eq_domain : Domain -> Domain -> bool.

Variable Codomain : Type.

Variable eq_codomain : Codomain -> Codomain -> Prop.

Variable undefined : Codomain.

(*****************************************************)
(*                                                   *)
(*  mappair is a pair consisting of an element from  *)
(*  domain and an element of the codomain which      *)
(*  represents an edge in the graph of the map.      *)
(*                                                   *)
(*****************************************************)

Record mappair : Type :=  {pre : Domain; post : Codomain}.


(*****************************************************)
(*                                                   *)
(*  map is a finite list of map pairs, we do not use *)
(*  the existing polylist, because map pair could be *)
(*  some thing not in Set, for example higher order  *)
(*  value.                                           *)
(*                                                   *)
(*****************************************************)

Inductive map : Type :=
  | null : map
  | add : mappair -> map -> map.


Fixpoint evaluate (m : map) : Domain -> Codomain :=
  match m with
  | null => fun d : Domain => undefined
  | add mp m1 =>
      fun d : Domain =>
      if eq_domain (pre mp) d then post mp else evaluate m1 d
  end.

Fixpoint refresh (m : map) : Domain -> Codomain -> map :=
  match m with
  | null => fun (d : Domain) (v : Codomain) => add (Build_mappair d v) null
  | add mp m1 =>
      fun (d : Domain) (v : Codomain) =>
      if eq_domain (pre mp) d
      then add (Build_mappair d v) m1
      else add mp (refresh m1 d v)
  end.

Fixpoint filter (m : map) : Domain -> map :=
  match m with
  | null => fun d : Domain => null
  | add mp m1 =>
      fun d : Domain =>
      if eq_domain (pre mp) d then m1 else add mp (filter m1 d)
  end.

Fixpoint domain (m : map) : list Domain :=
  match m with
  | null => nil (A:=Domain)
  | add mp m1 => pre mp :: domain m1
  end.

Fixpoint inclusion_map (m1 : map) : map -> Prop :=
  match m1 with
  | null => fun m2 : map => True
  | add mp m1' =>
      fun m2 : map =>
      eq_codomain (evaluate m2 (pre mp)) (post mp) /\ inclusion_map m1' m2
  end.

Definition eq_map (m1 m2 : map) : Prop :=
  inclusion_map m1 m2 /\ inclusion_map m2 m1.

End MAP_DEF.
