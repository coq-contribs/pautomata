(** p-Automates avec variables globales et locales 

    Une version des p-automates qui introduit un ensemble de noms de
    variables associées à des types. 

La synchronisation fait un produit sur les varaibles locales, 
permet de localiser certaines variables globales 
*)

Require Import PAutomata.

Set Implicit Arguments.
Unset Strict Implicit.
Section PAUTO.

Variable VarName : Set.
Variable TypeVarName : VarName -> Set.

Definition Vect (V : Set) (T : V -> Set) := forall v : V, T v.

Inductive Var (L : Set) : Set :=
  | Glob : VarName -> Var L
  | Local : L -> Var L.

Definition TypeVar (L : Set) (TL : L -> Set) (v : Var L) : Set :=
  match v with
  | Glob x => TypeVarName x
  | Local l => TL l
  end.

Definition VectVar (L : Set) (TL : L -> Set) := Vect (TypeVar TL).

Record VarLoc (local : VarName -> Prop) : Set := 
  {vlocname : VarName; is_local : local vlocname}.

Definition TypeVarLoc (local : VarName -> Prop) (v : VarLoc local) : Set :=
  TypeVarName (vlocname v).

Implicit Arguments TypeVarLoc [local].

Record PautL : Type := 
  {Vloc : Set; TVloc : Vloc -> Set; Paut : p_auto (VectVar TVloc)}.

Implicit Arguments TVloc [].

Variable I : Set.

Variable AutSync : I -> PautL.

Definition V (i : I) : Set := VectVar (TVloc (AutSync i)).

Definition Pauts (i : I) : p_auto (V i) := Paut (AutSync i).

Variable propre : VarName -> Prop.
Hypothesis propre_dec : forall v : VarName, {propre v} + {~ propre v}.

Inductive VarsyncL : Set :=
  | Propre : forall x : VarName, propre x -> VarsyncL
  | LocaleI : forall i : I, Vloc (AutSync i) -> VarsyncL.

Definition TVarsyncL (v : VarsyncL) : Set :=
  match v with
  | Propre x _ => TypeVarName x
  | LocaleI i l => TVloc (AutSync i) l
  end.


Definition Varsync := VectVar TVarsyncL.

Definition Var_proj (i : I) (Vx : Varsync) : V i :=
  fun v : Var (Vloc (AutSync i)) =>
  match v return (TypeVar (TVloc (AutSync i)) v) with
  | Glob x =>
      if propre_dec x
      then fun p => Vx (Local (Propre p))
      else fun _ => Vx (Glob VarsyncL x)
  | Local l => Vx (Local (LocaleI l))
  end.

Definition Locsyncs := forall i : I, Loc (Pauts i).
Definition Actsyncs := forall i : I, option (P_Act (Pauts i)).
Variable Vect_sync : Actsyncs -> Prop.

Definition PautoL_sync_mult :=
  Build_PautL (Pauto_sync_mult Var_proj Vect_sync).
   
End PAUTO.

Implicit Arguments Build_VarLoc [VarName].
Implicit Arguments TypeVarLoc [VarName].