(*i 	$Id$	 i*)

(**           
Definition and Interpretation of p-automata     
Emmanuel Freund \& Christine Paulin-Mohring               
July 1st 2000 
Modular version 
Christine Paulin-Mohring   
November 2002
*)

(*i*)
Require Export Time.
Require Import TimeSyntax.
Require Import TransMod.
(*i*)

Set Implicit Arguments.
Unset Strict Implicit.

(*s 
   An invariant is a set of triples [(l,s,v)]
   with [l] a location, [s] the clock value and [v] a variable 
*)

Definition P_Invariant (V : Type) (L : Set) := L -> Time -> V -> Prop.

(* Une transition est un ensemble de six-tuplets (a,s,l1,v1,l2,v2) 
   avec a une action, s la valeur de l'horloge, l1 la place initiale, v1, 
   la valeur initiale des variables, l2 la place finale et v2 la valeur finale des variables *)
Definition P_Transitions (V : Type) (L A : Set) :=
  A -> Time -> L -> V -> L -> V -> Prop.

Record p_auto (V : Type) : Type := mk_auto
  {P_Loc : Set;
   P_Inv : P_Invariant V P_Loc;
   P_Act : Set;
   P_Trans : P_Transitions V P_Loc P_Act}.

Implicit Arguments P_Inv [V].
Implicit Arguments P_Trans [V].

Module Type Pauto_obj.
Parameter Var : Type.
Parameter Pauto : p_auto Var.
End Pauto_obj.


Module Type Pauto_struct.
(*s Variables domain *)
Parameter Var : Type.

(* A p-automata on the [Var] domain for variables is built from a set 
   [Loc] of locations, an invariant [Inv] on these locations, a set of actions 
   and a set of transitions *)

Parameter Loc : Set.
Parameter Inv : P_Invariant Var Loc.
Parameter Act : Set.
Parameter Trans : P_Transitions Var Loc Act.

End Pauto_struct.


Module Pauto_struct_to_obj (P: Pauto_struct).
Definition Var := P.Var.
Definition Pauto : p_auto Var := mk_auto P.Inv P.Trans.
End Pauto_struct_to_obj.

Module Pauto_obj_to_struct (P: Pauto_obj).
Definition Var := P.Var.
Definition Loc := P_Loc P.Pauto.
Definition Inv := P_Inv P.Pauto.
Definition Act := P_Act P.Pauto.
Definition Trans := P_Trans P.Pauto.
End Pauto_obj_to_struct.

(** ** Transition systems associated to a p-automata *)

Module LTS_of (P: Pauto_struct).

(** Un état associé au p-automate est formé d'une place 
   d'une valeur d'horloge et d'une valeur pour les variables *)

Record P_state : Type := mk_state
  {loc_of : P.Loc; time_of : Time; val_of : P.Var}.

(* Les états admissibles sont ceux qui vérifient l'invariant *)
Definition adm (e : P_state) : Prop :=
  P.Inv (loc_of e) (time_of e) (val_of e).

(* [(temp_adm e dt)]
   si l'invariant reste satisfait pendant un intervalle de temps [dt] *)
Definition temp_adm (e : P_state) (dt : Time) : Prop :=
  forall T : Time,
  T0 </ T -> T <=/ dt -> P.Inv (loc_of e) (time_of e +/ T) (val_of e).

(* [(adm_until e t)] si l'invariant reste satisfait jusqu'au temps [t] *)
Definition adm_until (e : P_state) (t : Time) : Prop :=
  forall T : Time, time_of e </ T -> T <=/ t -> P.Inv (loc_of e) T (val_of e).


(* Les actions du système de transitions associé sont des actions discrètes 
   correspondant aux actions du p-automate ou bien des actions temporelles
   correspondant à l'écoulement du temps dans un état admissible *)

Inductive Act_time : Set :=
  | Dis : P.Act -> Act_time
  | Temp : Time -> Act_time.

(* Les transitions se font entre états admissibles *)

Inductive transitionI (e1 e2 : P_state) : Act_time -> Prop :=
  | trans_act :
      forall a : P.Act,
      P.Trans a (time_of e1) (loc_of e1) (val_of e1) (loc_of e2) (val_of e2) ->
      time_of e1 = time_of e2 -> transitionI e1 e2 (Dis a)
  | trans_temp :
      forall dt : Time,
      T0 <=/ dt ->
      e2 = mk_state (loc_of e1) (time_of e1 +/ dt) (val_of e1) ->
      temp_adm e1 dt -> transitionI e1 e2 (Temp dt).

Module I1.
Definition State := P_state.
Definition Act := Act_time.
Definition Trans : LTS_Transitions State Act :=
  fun e1 a e2 => transitionI e1 e2 a.
End I1.


(* Un deuxième système de transitions est obtenu en combinant les actions 
   temporelles et discrètes *)

Inductive P_trans_direct (e1 : P_state) (a : P.Act) (e2 : P_state) : Prop :=
    trans_direct_intro :
      time_of e1 <=/ time_of e2 ->
      adm_until e1 (time_of e2) ->
      P.Trans a (time_of e2) (loc_of e1) (val_of e1) (loc_of e2) (val_of e2) ->
      P_trans_direct e1 a e2.

Module I2.
Definition State := P_state.
Definition Act := P.Act.
Definition Trans : LTS_Transitions State Act :=
  fun e1 a e2 => P_trans_direct e1 a e2.
End I2.
End LTS_of.

(** ** Synchronisation of two p-automata :
 On se donne deux p-automates [Paut_1] et [Paut_2] sur deux ensembles 
    de variables distincts [Var1] et [Var2] , 
    le vecteur de synchronisation est un ensemble de couples [(a1,a2)]
    avec [a1] une action de [Paut_1] et [a2] une action de [Paut_2]
*)

Module Type Pauto_synchro.
 Declare Module P1 : Pauto_struct.
 Declare Module P2 : Pauto_struct.

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
End Pauto_synchro.

Module Synchro (Sync: Pauto_synchro).
Import Sync.

Definition Var := Varsync.
Definition Loc := (P1.Loc * P2.Loc)%type.
Definition Act := (P1.Act * P2.Act)%type.

(*s  Synchronisation of invariants  *)

Definition Inv : P_Invariant Var Loc :=
  fun l s v => P1.Inv (fst l) s (ProjVar1 v) /\ P2.Inv (snd l) s (ProjVar2 v).


(*s Synchronisation of transitions *)

Definition Trans : P_Transitions Var Loc Act :=
  fun a s l v l' v' =>
  Vectsync a /\
  P1.Trans (fst a) s (fst l) (ProjVar1 v) (fst l') (ProjVar1 v') /\
  P2.Trans (snd a) s (snd l) (ProjVar2 v) (snd l') (ProjVar2 v').
End Synchro.

Module SynchroProps (Sync: Pauto_synchro).
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
  let (l, t, v) := s in LTS1.mk_state (fst l) t (ProjVar1 v).

Definition Projstate2 (s : L.State) : L2.State :=
  let (l, t, v) := s in LTS2.mk_state (snd l) t (ProjVar2 v).

Theorem adm_synchro1 :
 forall e : L.State, LTS.adm e -> LTS1.adm (Projstate1 e).
unfold LTS.adm, LTS1.adm in |- *.
simple destruct 1.
case e; simpl in |- *; trivial.
Qed.

Theorem adm_synchro2 :
 forall e : L.State, LTS.adm e -> LTS2.adm (Projstate2 e).
unfold LTS.adm, LTS2.adm in |- *.
simple destruct 1.
case e; simpl in |- *; trivial.
Qed.

Theorem adm_synchro :
 forall e : L.State,
 LTS1.adm (Projstate1 e) -> LTS2.adm (Projstate2 e) -> LTS.adm e.
simple destruct e; simpl in |- *; repeat red in |- *; auto.
Qed.

End SynchroProps.

(*s Local Synchronisation *)
(* L'ensemble des variables du Pautomate synchronise *)
(* est le produit des ensembles des variables        *)

Module Type Pauto_synchro_loc.
  Declare Module P1 : Pauto_struct.
  Declare Module P2 : Pauto_struct.
  Parameter Vectsync : P1.Act * P2.Act -> Prop.
End Pauto_synchro_loc.

Module Synchro_loc (Sync: Pauto_synchro_loc).

Module struct.
Module P1 := Sync.P1.
Module P2 := Sync.P2.
Definition Vectsync := Sync.Vectsync.
Definition Varsync := prodT P1.Var P2.Var.
Definition ProjVar1 (v : Varsync) := fstT v.
Definition ProjVar2 (v : Varsync) := sndT v.
End struct.
Module pauto := Synchro struct.

End Synchro_loc.

(* Synchronisation of two p-automata *)

Module Type Pauto_synchro_glob.
  Declare Module P1 : Pauto_struct.
  Declare Module P2 : Pauto_struct with Definition Var := P1.Var.
  Parameter Vectsync : P1.Act * P2.Act -> Prop.
End Pauto_synchro_glob.

Module Synchro_glob (Sync: Pauto_synchro_glob).

Module struct.
Module P1 := Sync.P1.
Module P2 := Sync.P2.
Definition Vectsync := Sync.Vectsync.
Definition Varsync := P1.Var.
Definition ProjVar1 (v : Varsync) := v.
Definition ProjVar2 (v : Varsync) := v.
End struct.
Module pauto := Synchro struct.
End Synchro_glob.

(* ** Synchronisation d'une famille d'automates *)

Definition opt_vect (I : Set) (V : I -> Set) := forall i : I, option (V i).

Module Type Pauto_synchro_family.

Parameter I : Set.
Parameter V : I -> Set.
Parameter Pauts : forall i : I, p_auto (V i).
Parameter Varsync : Set.
Parameter Var_proj : forall i : I, Varsync -> V i.
(** Actions are defined as vectors partially defined from actions on each component, 
    an epsilon transition is introduced for undefined synchronisations, 
    a default transformation of variables is introduced *)
Parameter Actsync : Set.
Parameter EpsInterp : forall i : I, V i -> V i -> Prop.
Parameter
  Vectsync : Actsync -> opt_vect (fun i : I => P_Act (Pauts i)) -> Prop.
End Pauto_synchro_family.

Module Synchro_fam (Sync: Pauto_synchro_family).
Import Sync.

Definition Var := Varsync.
Definition Loc := forall i : I, P_Loc (Pauts i).
Definition Act := Actsync.

Definition Inv : P_Invariant Var Loc :=
  fun l s v => forall i : I, P_Inv (Pauts i) (l i) s (Var_proj i v).

Definition Trans : P_Transitions Var Loc Act :=
  fun a s l v l' v' =>
  exists2 av : opt_vect (fun i : I => P_Act (Pauts i)),
    Vectsync a av &
    (forall i : I,
     match av i with
     | Some b =>
         P_Trans (Pauts i) b s (l i) (Var_proj i v) (l' i) (Var_proj i v')
     | None => l i = l' i /\ EpsInterp (Var_proj i v) (Var_proj i v')
     end).

End Synchro_fam.
