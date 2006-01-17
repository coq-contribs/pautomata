(** p-Automata with global and local variables

    Christine Paulin & Bertrand Tavernier may 2002

    p-automata with an explicit set of names for variables 
    associated with their types (using dependent types) 

During synchronisation, the local variables of the synchronised product 
are a vector of local variables of each individual automata. A subset 
of global variables is localised for further synchronisation 
*)

Require Import PAutomataMod.

Set Implicit Arguments.
Unset Strict Implicit.


(** The vector of variables is defined in a dependent function type *)
Definition Vect (V : Set) (T : V -> Set) := forall v : V, T v.

(** A set of variables names with their types *)
Module Type VarNames.
Parameter V : Set.
Parameter TV : V -> Set.
End VarNames.


(** * The AutoL structure is parameterized by a set of var names associated with 
      their type *)

Module AutoL_general (G: VarNames).

(** Variables defined as either local or global *)
Inductive Vars (L : Set) : Set :=
  | Glob : G.V -> Vars L
  | Local : L -> Vars L.

(** Type of variables *)
Definition TVars (L : Set) (TL : L -> Set) (v : Vars L) : Set :=
  match v with
  | Glob x => G.TV x
  | Local l => TL l
  end.

(** A variable will be a vector indexed by name of variables *)
Definition VectVar (L : Set) (TL : L -> Set) := Vect (TVars TL).

Module AutoLVars (L: VarNames) : VarNames.
Definition V := Vars L.V.
Definition TV := TVars L.TV.
End AutoLVars.

Module Type Localize_struct.
Parameter local : G.V -> Prop.
End Localize_struct.

Module Localize (L: Localize_struct).
(** Localisation of a subset of global variables *)
Record VarLoc : Set := mkVarLoc {vlocname : G.V; is_local : L.local vlocname}.
Implicit Arguments mkVarLoc [].
Definition V := VarLoc.
Definition TV (v : V) : Set := G.TV (vlocname v).
End Localize.

  (** A localized automata is given by a set of local names, 
  the type of these variables and a p-automata built on the
  corresponding vector of variables *) 
 
Record PautL : Type := mk_autol
  {Loc : Set; TLoc : Loc -> Set; Paut : p_auto (VectVar TLoc)}.
Implicit Arguments TLoc [].

Definition P_LocL (p : PautL) := P_Loc (Paut p).
Definition P_ActL (p : PautL) := P_Act (Paut p).

Module Type AutoL_obj.
Parameter autoL : PautL.
End AutoL_obj.

Module Type AutoL_struct.
Declare Module L : VarNames.
Parameter Loc : Set.
Parameter Act : Set.
Parameter Inv : P_Invariant (VectVar L.TV) Loc.
Parameter Trans : P_Transitions (VectVar L.TV) Loc Act.
End AutoL_struct.

Module AutoL_obj_to_struct (P: AutoL_obj).
Module L.
  Definition V := Loc P.autoL.
  Definition TV := TLoc P.autoL.
End L.
Definition P := Paut P.autoL.
Definition Loc := P_Loc P.
Definition Inv := P_Inv P.
Definition Act := P_Act P.
Definition Trans := P_Trans P.
End AutoL_obj_to_struct.


(** * The p-automata associated to a localised automata structure *)
Module AutoL_to_Pauto (A: AutoL_struct). (* : Pauto_struct. *)
Definition Var := VectVar A.L.TV.
Definition Loc := A.Loc.
Definition Inv := A.Inv.
Definition Act := A.Act.
Definition Trans := A.Trans.
End AutoL_to_Pauto.


Module AutoL_struct_to_obj (P: AutoL_struct). (* : AutoL_obj *)
Module pauto_struct := AutoL_to_Pauto P.
Module pauto_obj := Pauto_struct_to_obj pauto_struct.
Definition autoL : PautL := mk_autol pauto_obj.Pauto.
End AutoL_struct_to_obj.

Module AutoL_to_LTS (A: AutoL_struct). (* : LTS_struct. *)
Module Pauto := AutoL_to_Pauto A.
Module LTS_of := PAutomataMod.LTS_of Pauto.
End AutoL_to_LTS.

Module AutoL_obj_to_LTS (A: AutoL_obj). (* : LTS_struct. *)
Module A_struct := AutoL_obj_to_struct A.
Module Pauto := AutoL_to_Pauto A_struct.
Module LTS_of := PAutomataMod.LTS_of Pauto.
End AutoL_obj_to_LTS.

(** * Synchronisation of a family of localised automata *)
Module Type AutoL_synchro_family.
Parameter I : Set.
Parameter AutoLs : I -> PautL.

Parameter propre : G.V -> Prop.
Parameter propre_dec : forall v : G.V, {propre v} + {~ propre v}.

Parameter Actsync : Set.
Parameter
  Vectsync : Actsync -> opt_vect (fun i : I => P_ActL (AutoLs i)) -> Prop.
End AutoL_synchro_family.

Module AutoL_synchro (Sync: AutoL_synchro_family).

(** Local variables of synchronized automata will be either 
    global variables "propre" or local variables indexed 
*)

Import Sync.

Inductive Lsync : Set :=
  | Propre : forall x : G.V, propre x -> Lsync
  | LocaleI : forall i : I, Loc (AutoLs i) -> Lsync.

Definition TLsync (v : Lsync) : Set :=
  match v with
  | Propre x _ => G.TV x
  | LocaleI i l => TLoc (AutoLs i) l
  end.

Module Sync_par.

Definition I := I.
Definition V (i : I) : Set := VectVar (TLoc (AutoLs i)).

Definition Pauts (i : I) : p_auto (V i) := Paut (AutoLs i).

Definition Varsync := VectVar TLsync.

Definition Var_proj (i : I) (Vx : Varsync) : V i :=
  fun v =>
  match v as x return (TVars (TLoc (AutoLs i)) x) with
  | Glob x =>
      match propre_dec x with
      | left p => Vx (Local (Propre p))
      | right _ => Vx (Glob Lsync x)
   end
  | Local l => Vx (Local (LocaleI l))
  end.

(** An epsilon transition is interpreted as unchanged on local variables 
    and an arbitrary change on globl variables *)

Definition EpsInterp (i : I) (vect vect' : V i) : Prop :=
  forall v : Vars (Loc (AutoLs i)),
  match v with
  | Glob x => True
  | Local l => vect v = vect' v
  end.

Definition Actsync := Actsync.
Definition Vectsync := Vectsync.
End Sync_par.

Module PautoSync := Synchro_fam Sync_par.
Module PautoSync_obj := Pauto_struct_to_obj PautoSync.

Module AutoLSync.
Definition LName : Set := Lsync.
Definition TLName : LName -> Set := TLsync.
Definition Auto : p_auto (VectVar TLName) := PautoSync_obj.Pauto.
End AutoLSync.

Definition AutoL_sync : PautL := mk_autol PautoSync_obj.Pauto.

Module AutoL_obj.
Definition Pauto := AutoL_sync.
End AutoL_obj.

End AutoL_synchro.
End AutoL_general.

(*
Implicits Build_VarLoc [1].
Implicits TypeVarLoc [1].
*)