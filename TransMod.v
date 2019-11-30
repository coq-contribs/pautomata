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
(* 	           Emmanuel Freund & Christine Paulin-Mohring               *)
(*                               July 1st 2000                              *)
(****************************************************************************)
(*i $Id$ i*)

Set Implicit Arguments.
Unset Strict Implicit.

(** * Modelisation of a labelled transition system *)
(** Modular version November 2002 *)

(** ** Definition of the module structure *)

Definition LTS_Transitions (S : Type) (A : Set) := S -> A -> S -> Prop.

Module Type LTS_struct.
Parameter State : Type.
Parameter Act : Set.
Parameter Trans : LTS_Transitions State Act.
End LTS_struct.


(** ** Expected properties of transition systems *)

Module LTS_prop (L: LTS_struct).
Import L.

(** *** [(access e1 e2)] when [e2] is reachable from [e1] *)
Inductive access (e1 : State) : State -> Prop :=
  | there : access e1 e1
  | add_acces :
      forall (e2 e3 : State) (t : Act),
      access e1 e2 -> Trans e2 t e3 -> access e1 e3. 

(** *** [(deadlock e)] when there is no more transition from [e] *)

Definition deadlock (e1 : State) : Prop :=
  forall (t : Act) (e2 : State), ~ Trans e1 t e2.

(** *** [(deadlock e)] when there is an infinite path from [e] *)

CoInductive vivacity : State -> Prop :=
    onemore :
      forall (t : Act) (e1 e2 : State),
      vivacity e2 -> Trans e1 t e2 -> vivacity e1.

(** *** [(InvStep P s0)] when [P] is preserved by transitions 
      from states accessible from [s0] *)
Definition InvStep (P : State -> Prop) (s0 : State) :=
  forall s s' : State,
  access s0 s -> forall a : Act, Trans s a s' -> P s -> P s'.

(** *** If [P] is preserved then it holds on states accessible from [s0] *)
Lemma Invariant :
 forall (s0 : State) (P : State -> Prop),
 InvStep P s0 -> P s0 -> forall s : State, access s0 s -> P s.
simple induction 3; intros; auto.
red in H.
apply H with e2 t; auto.
Qed.

End LTS_prop.

(* **  Synchronisation of two LTS *)
Module Type LTS_synchro.
Declare Module L1 : LTS_struct.
Declare Module L2 : LTS_struct.
Parameter SyncVect : L1.Act * L2.Act -> Prop.
End LTS_synchro.

Module Synchro (Sync: LTS_synchro) : LTS_struct.
Import Sync.

Definition Act : Set := (L1.Act * L2.Act)%type.

Definition State : Type := prodT L1.State L2.State.

Inductive trans (s : State) (a : Act) (s' : State) : Prop :=
    trans_both :
      SyncVect a ->
      L1.Trans (fstT s) (fst a) (fstT s') ->
      L2.Trans (sndT s) (snd a) (sndT s') -> trans s a s'.
Definition Trans := trans.

End Synchro.

(** ** Another synchronisation *)
(** Execute at the same time a synchronisation and a restriction of 
    the set of States 
*)

Module Type LTS_synchro_restr.
Declare Module L1 : LTS_struct.
Declare Module L2 : LTS_struct.
Parameter SyncVect : L1.Act * L2.Act -> Prop.
Parameter P : prodT L1.State L2.State -> Prop.
End LTS_synchro_restr.

Module SynchroRestr (Sync: LTS_synchro_restr) : LTS_struct.
Import Sync.

Definition Act : Set := (L1.Act * L2.Act)%type.

Definition State : Type := prodT L1.State L2.State.

Inductive trans (s : State) (a : Act) (s' : State) : Prop :=
    trans_both_restr :
      SyncVect a ->
      P s ->
      P s' ->
      L1.Trans (fstT s) (fst a) (fstT s') ->
      L2.Trans (sndT s) (snd a) (sndT s') -> trans s a s'.

Definition Trans := trans.
       
End SynchroRestr.


(** * Strong bisimulation *)

(** ** Two definitions, proof of equivalence *)

Module Bisimulation (L: LTS_struct).

Import L.

(** *** Definition of [R] is a bisimulation *)
Definition StBisimulation (R : State -> State -> Prop) : Prop :=
  forall p q : State,
  R p q ->
  (forall (a : Act) (p' : State),
   Trans p a p' -> exists2 q' : State, Trans q a q' & R p' q') /\
  (forall (a : Act) (q' : State),
   Trans q a q' -> exists2 p' : State, Trans p a p' & R p' q').

(**  *** When [R] is symmetric it is enough to check one direction *)

Lemma StBisimulation_sym_intro :
 forall R : State -> State -> Prop,
 (forall x y : State, R x y -> R y x) ->
 (forall p q : State,
  R p q ->
  forall (a : Act) (p' : State),
  Trans p a p' -> exists2 q' : State, Trans q a q' & R p' q') ->
 StBisimulation R.
intros.
split; intros.
apply H0 with (1 := H1); trivial.
elim H0 with q p a q'; auto; intros p' H3 H4.
exists p'; auto.
Qed.


(** *** Two States are equivalents when a bisimulation exists*)
Inductive StBEquiv (p q : State) : Prop :=
    exist :
      forall R : State -> State -> Prop,
      R p q -> StBisimulation R -> StBEquiv p q.

(* ** Direct coinductive definition *)
CoInductive StateEquiv : State -> State -> Prop :=
    StateEquiv_intro :
      forall p q : State,
      (forall (a : Act) (p' : State),
       Trans p a p' -> exists2 q' : State, Trans q a q' & StateEquiv p' q') ->
      (forall (a : Act) (q' : State),
       Trans q a q' -> exists2 p' : State, Trans p a p' & StateEquiv p' q') ->
      StateEquiv p q.

(** *** Properties of [StateEquiv] *)
Lemma StateEquiv_refl : forall p : State, StateEquiv p p.
cofix StateEquiv_refl.
intro; constructor; intros.
exists p'; auto.
exists q'; auto.
Qed.

Lemma StateEquiv_sym : forall p q : State, StateEquiv p q -> StateEquiv q p.
cofix StateEquiv_sym.
simple destruct 1; intros; constructor; intros.
case H1 with a p'; intros; trivial.
exists x; auto.
case H0 with a q'; intros; trivial.
exists x; auto.
Qed.

Lemma StateEquiv_trans :
 forall p q r : State, StateEquiv p q -> StateEquiv q r -> StateEquiv p r.
cofix StateEquiv_trans; intros p q r H1.
case H1; clear H1 p q; intros.
inversion_clear H1; intros.
constructor; intros.
case H with (1 := H1); intros.
case H2 with (1 := H4); intros.
exists x0; eauto.
case H3 with (1 := H1); intros.
case H0 with (1 := H4); intros.
exists x0; eauto.
Qed.

Lemma State_Equiv_bisim : StBisimulation StateEquiv.
constructor.
case H; auto.
case H; auto.
Qed.

(** ** Equivalence of the two definitions *)

Lemma StateEquiv_StBEquiv :
 forall p q : State, StateEquiv p q -> StBEquiv p q.
exists StateEquiv; trivial.
exact State_Equiv_bisim.
Qed.

Lemma StBEquiv_StateEquiv :
 forall p q : State, StBEquiv p q -> StateEquiv p q.
simple destruct 1; intros R Rpq Bi; generalize p q Rpq.
cofix StBEquiv_StateEquiv; intros.
case Bi with (1 := Rpq0); intros.
constructor; intros.
case H0 with (1 := H2); intros.
exists x; auto.
case H1 with (1 := H2); intros.
exists x; auto.
Qed.

(** *** Direct proof of properties of [StBEquiv] *)

Lemma StEquiv_Refl : forall p : State, StBEquiv p p.
intro; exists (fun p q : State => p = q); trivial.
split; intros.
exists p'; trivial.
rewrite <- H; trivial.
exists q'; trivial.
rewrite H; trivial. 
Qed.

Lemma StEquiv_Sym : forall p q : State, StBEquiv p q -> StBEquiv q p.
intros.
case H; intros.
exists (fun p q : State => R q p); trivial.
red in |- *; intros.
case H1 with (1 := H2); auto.
Qed.

Lemma StEquiv_Trans :
 forall p q r : State, StBEquiv p q -> StBEquiv q r -> StBEquiv p r.
intros p q r H1 H2; case H1; case H2; clear H1 H2; intros.
exists (fun p r : State => exists2 q : State, R0 p q & R q r).
exists q; auto.
red in |- *; intros.
case H3; clear H3; intros.
case H2 with (1 := H3); clear H2; intros.
case H0 with (1 := H4); clear H0; intros.
split; intros.
case H2 with (1 := H7); clear H2; intros.
case H0 with (1 := H2); clear H0; intros.
exists x1; trivial; exists x0; trivial.
case H6 with (1 := H7); clear H6; intros.
case H5 with (1 := H6); clear H5; intros.
exists x1; trivial; exists x0; trivial.
Qed.

End Bisimulation.


