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
      match propre_dec x with
      | left p => Vx (Local (Propre p))
      | right _ => Vx (Glob VarsyncL x)
      end
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