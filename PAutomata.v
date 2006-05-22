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

(*s          
Definition and Interpretation of p-automata     
Emmanuel Freund \& Christine Paulin-Mohring               
July 1st 2000 
*)

Require Import Time.
Require Import TimeSyntax.
Require Import Transitions.

Set Implicit Arguments.
Unset Strict Implicit.

(*s P-automata definition *)
Section PAUTO_DEF.

(*s Variables domain *)
Variable V : Type.

(*s 
   An invariant is a set of triples [(l,s,v)]
   with [l] a location, [s] the clock value and [v] a variable 
*)

Definition P_Invariant (L : Set) := L -> Time -> V -> Prop.

(* Une transition est un ensemble de six-tuplets (a,s,l1,v1,l2,v2) 
   avec a une action, s la valeur de l'horloge, l1 la place initiale, v1, 
   la valeur initiale des variables, l2 la place finale et v2 la valeur finale des variables *)
Definition P_Transitions (L A : Set) := A -> Time -> L -> V -> L -> V -> Prop.

(* Un p-automate sur le domaine V est formé d'un ensemble de places Loc, d'un invariant sur 
   ces places, d'un ensemble d'actions Act et d'un ensemble de transitions *)

Record p_auto : Type := 
  {Loc : Set;
   P_Inv : P_Invariant Loc;
   P_Act : Set;
   P_Trans : P_Transitions Loc P_Act}.


End PAUTO_DEF.

(*s Transition system associated to a p-automata *)

Section TRANSITIONS.

Variable V : Type.
Variable P : p_auto V.

(* Un état associé au p-automate est formé d'une place 
   d'une valeur d'horloge et d'une valeur pour les variables *)

Record P_state : Type :=  {loc_of : Loc P; time_of : Time; val_of : V}.

(* Les états admissibles sont ceux qui vérifient l'invariant *)
Definition adm (e : P_state) : Prop :=
  P_Inv (loc_of e) (time_of e) (val_of e).

(* [(temp_adm e dt)]
   si l'invariant reste satisfait pendant un intervalle de temps [dt] *)
Definition temp_adm (e : P_state) (dt : Time) : Prop :=
  forall T : Time,
  T0 </ T -> T <=/ dt -> P_Inv (loc_of e) (time_of e +/ T) (val_of e).

(* [(adm_until e t)] si l'invariant reste satisfait jusqu'au temps [t] *)
Definition adm_until (e : P_state) (t : Time) : Prop :=
  forall T : Time, time_of e </ T -> T <=/ t -> P_Inv (loc_of e) T (val_of e).


(* Les actions du système de transitions associé sont des actions discrètes 
   correspondant aux actions du p-automate ou bien des actions temporelles
   correspondant à l'écoulement du temps dans un état admissible *)

Inductive Act_time : Set :=
  | Dis : P_Act P -> Act_time
  | Temp : Time -> Act_time.

(* Les transitions se font entre états admissibles *)

Inductive transitionI (e1 e2 : P_state) : Act_time -> Prop :=
  | trans_act :
      forall a : P_Act P,
      P_Trans a (time_of e1) (loc_of e1) (val_of e1) (loc_of e2) (val_of e2) ->
      time_of e1 = time_of e2 -> transitionI e1 e2 (Dis a)
  | trans_temp :
      forall dt : Time,
      T0 <=/ dt ->
      e2 = Build_P_state (loc_of e1) (time_of e1 +/ dt) (val_of e1) ->
      temp_adm e1 dt -> transitionI e1 e2 (Temp dt).

Definition P_transition : LTS_Transitions P_state Act_time :=
  fun e1 a e2 => transitionI e1 e2 a.

Definition P_auto_LTS : LTS := Build_LTS P_transition.

Definition P_stable (inv : P_state -> Prop) :=
  forall (x y : P_state) (a : Act_time), P_transition x a y -> inv x -> inv y.

(* Un deuxième système de transitions est obtenu en combinant les actions 
   temporelles et discrètes *)

Inductive P_trans_direct (e1 : P_state) (a : P_Act P) 
(e2 : P_state) : Prop :=
    trans_direct_intro :
      time_of e1 <=/ time_of e2 ->
      adm_until e1 (time_of e2) ->
      P_Trans a (time_of e2) (loc_of e1) (val_of e1) (loc_of e2) (val_of e2) ->
      P_trans_direct e1 a e2.

Definition P_auto_LTS_direct : LTS := Build_LTS P_trans_direct.


End TRANSITIONS.

(*s Synchronisation of two p-automata :
 On se donne deux p-automates [Paut_1] et [Paut_2] sur deux ensembles 
    de variables distincts [Var1] et [Var2] , 
    le vecteur de synchronisation est un ensemble de couples [(a1,a2)]
    avec [a1] une action de [Paut_1] et [a2] une action de [Paut_2]
*)

Section SYNCHRONISATION.

(*s                                                 *)
(*        [Lsync] = produit des locations           *)
(*        [Actsync] = produit etendu des actions    *)
(*        [Vectsync] = vecteur de synchronisation   *)

Variable Var1 Var2 : Type.
Variable Paut_1 : p_auto Var1.
Variable Paut_2 : p_auto Var2.
Let L1 : Set := Loc Paut_1.
Let L2 : Set := Loc Paut_2.
Let act1 := P_Act Paut_1.
Let act2 := P_Act Paut_2.

Definition Locsync := (L1 * L2)%type.
Definition Actsync := (act1 * act2)%type.
Variable Vectsync : Actsync -> Prop.


(*s Generalised synchronisation                                    *)
(*  [Varsync] est l'ensemble des variables du Pautomate synchronise. *)
(*  [FineProj] verifie que cet ensemble est bien fonde.              *)


Section SYNCHRO_GEN.

Variable Varsync : Type.
Variable ProjVar1 : Varsync -> Var1.
Variable ProjVar2 : Varsync -> Var2.


Definition FineProj : Prop :=
  forall v v' : Varsync,
  ProjVar1 v = ProjVar1 v' -> ProjVar2 v = ProjVar2 v' -> v = v'.

(*s  Synchronisation of invariants  *)

Definition Invsync : P_Invariant Varsync Locsync :=
  fun l s v => P_Inv (fst l) s (ProjVar1 v) /\ P_Inv (snd l) s (ProjVar2 v).


(*s Synchronisation of transitions *)

Definition Transsync : P_Transitions Varsync Locsync Actsync :=
  fun a s l v l' v' =>
  Vectsync a /\
  P_Trans (fst a) s (fst l) (ProjVar1 v) (fst l') (ProjVar1 v') /\
  P_Trans (snd a) s (snd l) (ProjVar2 v) (snd l') (ProjVar2 v').

(*s The synchronised p-automata *)

Definition Pauto_sync : p_auto Varsync := Build_p_auto Invsync Transsync.


(*s Quelques resultats sur la synchronisation des etats *****)

Definition P_statesync := P_state Pauto_sync.

Definition Projstate1 (s : P_statesync) : P_state Paut_1 :=
  let (l, t, v) := s in Build_P_state (fst l) t (ProjVar1 v).

Definition Projstate2 (s : P_statesync) : P_state Paut_2 :=
  let (l, t, v) := s in Build_P_state (snd l) t (ProjVar2 v).

Theorem adm_synchro1 : forall e : P_statesync, adm e -> adm (Projstate1 e).
unfold adm in |- *.
simple destruct 1.
case e; simpl in |- *; trivial.
Qed.

Theorem adm_synchro2 : forall e : P_statesync, adm e -> adm (Projstate2 e).
unfold adm in |- *.
simple destruct 1.
case e; simpl in |- *; trivial.
Qed.

Theorem adm_synchro :
 forall e : P_statesync, adm (Projstate1 e) -> adm (Projstate2 e) -> adm e.
simple destruct e; simpl in |- *; red in |- *; auto.
Qed.

End SYNCHRO_GEN.

(*s Local Synchronisation *)
(* L'ensemble des variables du Pautomate synchronise *)
(* est le produit des ensembles des variables        *)

Section SYNCHRO_LOC.

Let Varsync := prodT Var1 Var2.
Let ProjVar1 (v : Varsync) := fstT v.
Let ProjVar2 (v : Varsync) := sndT v.
Definition Pauto_sync_loc : p_auto Varsync := Pauto_sync ProjVar1 ProjVar2.

End SYNCHRO_LOC.
End SYNCHRONISATION.

(* Synchronisation of two p-automata *)

Section SYNCHRO_GLOB.
Variable Var : Type.
Variable Paut1 Paut2 : p_auto Var.
Variable Vectsync : Actsync Paut1 Paut2 -> Prop.
Let Varsync := Var.
Let ProjVar1 (v : Varsync) := v.
Let ProjVar2 (v : Varsync) := v.

Definition Pauto_sync_glob : p_auto Varsync :=
  Pauto_sync Vectsync ProjVar1 ProjVar2.
End SYNCHRO_GLOB.


(* Synchronisation d'une famille d'automates *)

Section SYNCHRO_MULT.
(* Synchronisation multiple sur une famille de p-automates
  Une famille $(a_i)_{i \in I}$ est représentée comme une fonction de $i$ in $I $
  dans le type de $a_i$ qui peut lui même dépendre de $i$ *)

Variable I : Set.
Variable V : I -> Set.
Variable Pauts : forall i : I, p_auto (V i).
Variable Varsync : Set.
Variable Var_proj : forall i : I, Varsync -> V i.

Definition Locsyncs := forall i : I, Loc (Pauts i).
Definition Actsyncs := forall i : I, option (P_Act (Pauts i)).
Variable Vect_sync : Actsyncs -> Prop.

Definition InvS : P_Invariant Varsync Locsyncs :=
  fun l s v => forall i : I, P_Inv (l i) s (Var_proj i v).

Definition TransS : P_Transitions Varsync Locsyncs Actsyncs :=
  fun a s l v l' v' =>
  Vect_sync a /\
  (forall i : I,
   match a i with
   | Some b => P_Trans b s (l i) (Var_proj i v) (l' i) (Var_proj i v')
   | None => l i = l' i /\ Var_proj i v = Var_proj i v'
   end).

Definition Pauto_sync_mult : p_auto Varsync := Build_p_auto InvS TransS.

End SYNCHRO_MULT.

