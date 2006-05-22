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


(*i 	$Id$	 i*)

(**           
Definition and Interpretation of generalized hybrid automata 

Set of locations
Set of variables
Set of actions
Invariants on Locations 
Two sorts of transitions
   - continuous transitions following an evolution relation on variables
preserving the invariant
   - discrete transitions on actions with arbitrary modification 
of variables
    
Bertrand Tavernier \& Christine Paulin-Mohring               
August 2004
*)

(*i*)
Require Import TransMod.
(*i*)

Set Implicit Arguments.
Set Strict Implicit.

(** 
   An invariant is a set of pairs [(l,v)]
   with [l] a location and [v] a variable 
*)
Definition G_Invariant (V : Type) (L : Set) := L -> V -> Prop.

(**
   A transition is a set of 5-uples (a,l1,v1,l2,v2) 
   with a an action, l1 the initial location, v1, 
   the initial value of variables, l2 the final location 
   and v2 the final value of variables *)
Definition G_Transitions (V : Type) (L A : Set) :=
  A -> L -> V -> L -> V -> Prop.

(**
   An evolution is a relation between variables depending on the location 
   which control the continuous transitions. 
   The invariant can be integrated in this relation.
*)

Definition G_Evolution (V : Type) (L : Set) := L -> V -> V -> Prop.

Record g_auto (V : Type) : Type := mk_gauto
  {G_Loc : Set;
   G_Evo : G_Evolution V G_Loc;
   G_Act : Set;
   G_Trans : G_Transitions V G_Loc G_Act}.


Module Type Gauto_obj.
Parameter Var : Type.
Parameter Gauto : g_auto Var.
End Gauto_obj.


Module Type Gauto_struct.
(*s Variables domain *)
Parameter Var : Type.

(* A g-automata on the [Var] domain for variables is built from a set 
   [Loc] of locations, an evolution relation [Evo] on these locations, 
   a set of actions 
   and a set of transitions *)

Parameter Loc : Set.
Parameter Evo : G_Evolution Var Loc.
Parameter Act : Set.
Parameter Trans : G_Transitions Var Loc Act.

End Gauto_struct.


Module Gauto_struct_to_obj (P: Gauto_struct).
Definition Var := P.Var.
Definition Gauto : g_auto Var := mk_gauto P.Evo P.Trans.
End Gauto_struct_to_obj.

Module Gauto_obj_to_struct (P: Gauto_obj).
Definition Var := P.Var.
Definition Loc := G_Loc P.Gauto.
Definition Evo := G_Evo P.Gauto.
Definition Act := G_Act P.Gauto.
Definition Trans := G_Trans P.Gauto.
End Gauto_obj_to_struct.

(** ** Transition systems associated to a g-automata *)

Module LTS_of (P: Gauto_struct).

(** The state associated with the g-automata is built from the location 
    and the value of variables *)

Record G_state : Type := mk_state
  {loc_of : P.Loc; val_of : P.Var}.


(**
   Actions are either discrete actions corresponding to transitions 
   in the g-automata or continuous actions corresponding to a possible
   evolution.
*)

Inductive Act_time : Set :=
  | Dis : P.Act -> Act_time
  | Temp : Act_time.


Inductive transitionI (e1 e2 : G_state) : Act_time -> Prop :=
  | trans_act :
      forall a : P.Act,
      P.Trans a (loc_of e1) (val_of e1) (loc_of e2) (val_of e2) ->
      transitionI e1 e2 (Dis a)
  | trans_temp :
      P.Evo (loc_of e1) (val_of e1) (val_of e2)
      -> (loc_of e1)=(loc_of e2) -> transitionI e1 e2 Temp.

Module I1.
Definition State := G_state.
Definition Act := Act_time.
Definition Trans : LTS_Transitions State Act :=
  fun e1 a e2 => transitionI e1 e2 a.
End I1.


(* A second transition system combining continuous and discrete transitions *)

Inductive P_trans_direct (e1 : G_state) (a : P.Act) (e2 : G_state) : Prop :=
    trans_direct_intro :
      forall v, P.Evo (loc_of e1) (val_of e1) v ->
      P.Trans a (loc_of e1) v (loc_of e2) (val_of e2) ->
      P_trans_direct e1 a e2.

Module I2.
Definition State := G_state.
Definition Act := P.Act.
Definition Trans : LTS_Transitions State Act :=
  fun e1 a e2 => P_trans_direct e1 a e2.
End I2.
End LTS_of.

(** ** Synchronisation of two g-automata :
 On se donne deux g-automates [Paut_1] et [Paut_2] sur deux ensembles 
    de variables distinctes [Var1] et [Var2] , 
    le vecteur de synchronisation est un ensemble de couples [(a1,a2)]
    avec [a1] une action de [Paut_1] et [a2] une action de [Paut_2]
*)

Module Type Gauto_synchro.
 Declare Module P1 : Gauto_struct.
 Declare Module P2 : Gauto_struct.

(** A general set of variables   
Two projections function satisfying 
[Definition FineProj : Prop :=
        (v,v' : Varsync) (ProjVar1 v) == (ProjVar1 v')
                    -> (ProjVar2 v) == (ProjVar2 v') -> (v == v').]
*)
  Parameter Varsync : Type.
  Parameter ProjVar1 : Varsync -> P1.Var.
  Parameter ProjVar2 : Varsync -> P2.Var.
(** Synchronisation vector *)
  Parameter Vectsync : P1.Act * P2.Act -> Prop.
End Gauto_synchro.

Module Synchro (Sync: Gauto_synchro).
Import Sync.

Definition Var := Varsync.
Definition Loc := (P1.Loc * P2.Loc)%type.
Definition Act := (P1.Act * P2.Act)%type.

(*s  Synchronisation of evolutions  *)

Definition Evo : G_Evolution Var Loc :=
  fun l v w => P1.Evo (fst l) (ProjVar1 v) (ProjVar1 w) 
            /\ P2.Evo (snd l) (ProjVar2 v) (ProjVar2 w) .


(*s Synchronisation of transitions *)

Definition Trans : G_Transitions Var Loc Act :=
  fun a l v l' v' =>
  Vectsync a /\
  P1.Trans (fst a) (fst l) (ProjVar1 v) (fst l') (ProjVar1 v') /\
  P2.Trans (snd a) (snd l) (ProjVar2 v) (snd l') (ProjVar2 v').
End Synchro.

Module SynchroProps (Sync: Gauto_synchro).
Import Sync.
Module LTS1 := LTS_of P1.
Module L1 := LTS1.I1.
Module LTS2 := LTS_of P2.
Module L2 := LTS2.I1.
Module P := Synchro Sync.
Module LTS := LTS_of P.
Module L := LTS.I1.

(** * Quelques definitions et resultats sur la synchronisation des etats *)

Definition Projstate1 (s : L.State) : L1.State :=
  let (l, v) := s in LTS1.mk_state (fst l) (ProjVar1 v).

Definition Projstate2 (s : L.State) : L2.State :=
  let (l, v) := s in LTS2.mk_state (snd l) (ProjVar2 v).

End SynchroProps.

(*s Local Synchronisation *)
(* L'ensemble des variables du Pautomate synchronise *)
(* est le produit des ensembles des variables        *)

Module Type Gauto_synchro_loc.
  Declare Module P1 : Gauto_struct.
  Declare Module P2 : Gauto_struct.
  Parameter Vectsync : P1.Act * P2.Act -> Prop.
End Gauto_synchro_loc.

Module Synchro_loc (Sync: Gauto_synchro_loc).

Module struct.
Module P1 := Sync.P1.
Module P2 := Sync.P2.
Definition Vectsync := Sync.Vectsync.
Definition Varsync := prodT P1.Var P2.Var.
Definition ProjVar1 (v : Varsync) := fstT v.
Definition ProjVar2 (v : Varsync) := sndT v.
End struct.
Module gauto := Synchro struct.

End Synchro_loc.

(* Synchronisation of two p-automata *)

Module Type Gauto_synchro_glob.
  Declare Module P1 : Gauto_struct.
  Declare Module P2 : Gauto_struct with Definition Var := P1.Var.
  Parameter Vectsync : P1.Act * P2.Act -> Prop.
End Gauto_synchro_glob.

Module Synchro_glob (Sync: Gauto_synchro_glob).

Module struct.
Module P1 := Sync.P1.
Module P2 := Sync.P2.
Definition Vectsync := Sync.Vectsync.
Definition Varsync := P1.Var.
Definition ProjVar1 (v : Varsync) := v.
Definition ProjVar2 (v : Varsync) := v.
End struct.
Module gauto := Synchro struct.
End Synchro_glob.

(* ** Synchronisation of a family of automata *)

Definition opt_vect (I : Set) (V : I -> Set) 
   := forall i : I, option (V i).

Module Type Gauto_synchro_family.

Parameter I : Set.
Parameter V : I -> Set.
Parameter Pauts : forall i : I, g_auto (V i).
Parameter Varsync : Set.
Parameter Var_proj : forall i : I, Varsync -> V i.
(** Actions are defined as vectors partially defined from actions 
    on each component, 
    an epsilon transition is introduced for undefined synchronisations, 
    a default transformation of variables is introduced *)
Parameter Actsync : Set.
Parameter EpsInterp : forall i : I, V i -> V i -> Prop.
Parameter
  Vectsync : Actsync -> opt_vect (fun i : I => G_Act (Pauts i)) -> Prop.
End Gauto_synchro_family.

Module Synchro_fam (Sync: Gauto_synchro_family).
Import Sync.

Definition Var := Varsync.
Definition Loc := forall i : I, G_Loc (Pauts i).
Definition Act := Actsync.

Definition Evo : G_Evolution Var Loc :=
  fun l v w => forall i : I, G_Evo (Pauts i) (l i) (Var_proj i v) (Var_proj i w).

Definition Trans : G_Transitions Var Loc Act :=
  fun a l v l' v' =>
  exists2 av : opt_vect (fun i : I => G_Act (Pauts i)),
    Vectsync a av &
    (forall i : I,
     match av i with
     | Some b =>
         G_Trans (Pauts i) b (l i) (Var_proj i v) (l' i) (Var_proj i v')
     | None => l i = l' i /\ EpsInterp (Var_proj i v) (Var_proj i v')
     end).

End Synchro_fam.