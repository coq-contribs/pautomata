
(*****************************************************)
(*                       Var.v                       *)
(*                     Yijia CHEN                    *)
(*                                                   *)
(*****************************************************)

Require Import Bool.
Require Import List. (* for append operation *)

Require Import String.
Require Import Map.

Set Implicit Arguments.
Unset Strict Implicit.

(*****************************************************)
(*                                                   *)
(*  "typed value"                                    *)
(*                                                   *)
(*****************************************************)

Section TYPEDVALUE_DEF.

Record typedvalue : Type :=  {type : Type; content : type}.

Inductive utopia : Set :=
    fan : utopia.

Definition undefinedtypedvalue := Build_typedvalue fan. 

Definition eq_typedvalue := eq (A:=typedvalue).

Section PREDICATE_TYPEDVALUE_DEF.

Variable type1 : Type.
Variable type2 : Type.

Variable predicate1 : type1 -> Prop.

Definition predicate_typedvalue (tv : typedvalue) : Prop :=
  type tv = type1 /\
  (forall vr : type1, tv = Build_typedvalue vr -> predicate1 vr).

Variable predicate2 : type1 -> type2 -> Prop.

Definition predicate_type1_typedvalue2 (v1 : type1) 
  (tv2 : typedvalue) : Prop :=
  type tv2 = type2 /\
  (forall v2 : type2, tv2 = Build_typedvalue v2 -> predicate2 v1 v2).

Definition predicate_typedvalue1_type2 (tv1 : typedvalue) 
  (v2 : type2) : Prop :=
  type tv1 = type1 /\
  (forall v1 : type1, tv1 = Build_typedvalue v1 -> predicate2 v1 v2).

Definition predicate_typedvalue1_typedvalue2 (tv1 tv2 : typedvalue) : Prop :=
  type tv1 = type1 /\
  type tv2 = type2 /\
  (forall (v1 : type1) (v2 : type2),
   tv1 = Build_typedvalue v1 /\ tv2 = Build_typedvalue v2 -> predicate2 v1 v2).

End PREDICATE_TYPEDVALUE_DEF.

End TYPEDVALUE_DEF.


(*****************************************************)
(*                                                   *)
(*  "pvaluation" is the type of those mapping from   *)
(*  string to typed value.                           *)
(*                                                   *)
(*****************************************************)


Section PVALUATION_DEF.

Definition pvaluation := map string typedvalue.

Definition emptypvaluation := null string typedvalue.

Definition pvalue := evaluate eq_string undefinedtypedvalue.

Definition pupdate :=
  refresh (Domain:=string) eq_string (Codomain:=typedvalue).

Definition prestrict := filter eq_string.

Definition eq_pvaluation :=
  eq_map eq_string eq_typedvalue undefinedtypedvalue.

Definition defined (pv : pvaluation) (v : string) :=
  pvalue pv v <> undefinedtypedvalue.

Definition is_type (pv : pvaluation) (v : string) (t : Type) :=
  type (pvalue pv v) = t.
End PVALUATION_DEF.


(*
(*****************************************************)
(*                                                   *)
(*  "boolmap" is the type of those mapping from      *)
(*  string to boolean.                               *)
(*                                                   *)
(*****************************************************)

Section BOOLMAP_DEF.

Definition boolmap := (map string bool).

Definition emptyboolmap := (null string bool).

Definition boolvalue := (evaluate eq_string false).

Definition boolupdate := (!refresh string eq_string bool).

Definition boolrestrict := (filter eq_string).

End BOOLMAP_DEF.


(*****************************************************)
(*                                                   *)
(*  "pvaluation" is the type of those mapping from   *)
(*  string to typed value with explicit indication   *)
(*  of wether the variable is shared or local.       *)
(*                                                   *)
(*****************************************************)

Section PVALUATION_DEF.

Record pvaluation : Type :=
 { val : valuation;
   shared : boolmap }.

Definition emptypvaluation := (Build_pvaluation emptyvaluation emptyboolmap).

Definition pvalue : pvaluation -> string -> typedvalue
  := [pv : pvaluation]
       (evaluate eq_string undefinedtypedvalue (val pv)).

Definition pshared : pvaluation -> string -> bool
  := [pv : pvaluation] (evaluate eq_string false (shared pv)).

Definition pupdate : pvaluation -> string -> typedvalue -> bool -> pvaluation
  := [pv : pvaluation; str : string; v : typedvalue; sh : bool]
       (Build_pvaluation (update (val pv) str v)
                         (boolupdate (shared pv) str sh)).

Definition prestrict : pvaluation -> string -> pvaluation
  := [pv : pvaluation; str : string]
       (Build_pvaluation (restrict (val pv) str)
                         (boolrestrict (shared pv) str)).

Definition plocalise : pvaluation -> string -> pvaluation
  := [pv : pvaluation; str : string]
       (Build_pvaluation (val pv)
                         (boolupdate (shared pv) str false)).

End PVALUATION_DEF.


(*****************************************************)
(*                                                   *)
(*  "pvaljoin" defines the way how two pvaluations   *)
(*  are joined together and the way two projection   *)
(*  functions are derived.                           *)
(*                                                   *)
(*****************************************************)

Section PVALJOIN_DEF.


Fixpoint consistent1 [val1 : valuation] : valuation -> boolmap -> boolmap -> Prop
  := Cases val1 of
       null => [val2 : valuation; bm1, bm2 : boolmap] (true = true)
     | (add mp m1) => [val2 : valuation; bm1, bm2 : boolmap]
                        let var = (pre mp) in
                        if (boolvalue bm1 var)
                        then ((post mp) == (value val2 var))
                             /\ (consistent1 m1 val2 bm1 bm2)
                        else (consistent1 m1 val2 bm1 bm2)
     end.


Definition consistent : pvaluation -> pvaluation -> Prop
  := [pv1, pv2 : pvaluation] (consistent1 (val pv1) (val pv2) (shared pv1) (shared pv2)).



Definition tokenstring1 : string := (cons l (cons o (cons c (cons a voidstring)))).

Definition tokenstring2 : string := (cons l (cons o (cons c (cons b voidstring)))).

Fixpoint localisevaluation [val :valuation] : boolmap -> string -> valuation
  := Cases val of 
       null => [bm : boolmap; tokenstring : string] emptyvaluation
     | (add mp m1) => [bm : boolmap; tokenstring : string]
                        let var = (pre mp) in
                        if (boolvalue bm var)
                        then (update (localisevaluation m1 bm tokenstring) var (post mp))
                        else let newvar = (app tokenstring var) in
                        (update (localisevaluation m1 bm tokenstring) newvar (post mp))
     end.

Fixpoint mergevaluation [val1 : valuation] : valuation -> boolmap -> boolmap -> valuation
  := Cases val1 of
       null => [val2 : valuation; bm1, bm2 : boolmap] (localisevaluation val2 bm2 tokenstring2)
     | (add mp m1) => [val2 : valuation; bm1, bm2 : boolmap]
                          let var = (pre mp) in
                          if (boolvalue bm1 var)
                          then (update (mergevaluation m1 val2 bm1 bm2) var (post mp))
                          else let newvar = (app tokenstring1 var) in
                                (update (mergevaluation m1 val2 bm1 bm2) newvar (post mp))
     end.

Fixpoint localiseboolmap [bm :boolmap] : string -> boolmap
  := Cases bm of
       null => [tokenstring : string] emptyboolmap
     | (add mp m1) => [tokenstring : string]
                        let var = (pre mp) in
                        if (post mp)
                        then (boolupdate (localiseboolmap m1 tokenstring) var true)
                        else let newvar = (app tokenstring var) in
                             (boolupdate (localiseboolmap m1 tokenstring)
                                         newvar false)
     end.

Fixpoint mergeboolmap [bm1 : boolmap] : boolmap -> boolmap
  := Cases bm1 of
       null => [bm2 : boolmap] (localiseboolmap bm2 tokenstring2)
     | (add mp m1) => [bm2 : boolmap]
                          let var = (pre mp) in
                          if (post mp)
                          then (boolupdate (mergeboolmap m1 bm2) var true)
                          else let newvar = (app tokenstring1 var) in
                                (boolupdate (mergeboolmap m1 bm2) newvar false)
     end.

Definition mergepvaluation : pvaluation -> pvaluation -> pvaluation
  := [pv1, pv2 :pvaluation]
       (Build_pvaluation (mergevaluation (val pv1) (val pv2) (shared pv1) (shared pv2))
                         (mergeboolmap (shared pv1) (shared pv2))).

Fixpoint projection_string  [val : valuation] : boolmap -> string -> valuation
  := Cases val of
       null => [bm : boolmap; str : string] emptyvaluation
     | (add mp m1) => [bm : boolmap; str : string]
                          let var = (pre mp) in
                          if (boolvalue bm var)
                          then (update (projection_string m1 bm str) var (post mp))
                          else if (prefix_string var str)
                               then (update (projection_string m1 bm str)
                                            (extract_string var str) (post mp))
                               else (projection_string m1 bm str)
     end.

Fixpoint boolprojection_string [bm : boolmap] : string -> boolmap
  := Cases bm of
       null => [str : string] emptyboolmap
     | (add mp m1) => [str : string]
                           let var = (pre mp) in
                           if (post mp)
                           then (boolupdate (boolprojection_string m1 str) var true)
                           else if (prefix_string var str)
                                then (boolupdate (boolprojection_string m1 str)
                                             (extract_string var str) false)
                                else (boolprojection_string m1 str)
     end.

Definition projection1 : pvaluation -> pvaluation
  := [pv : pvaluation] (Build_pvaluation
                          (projection_string (val pv) (shared pv) tokenstring1)
                          (boolprojection_string (shared pv) tokenstring1)).


Definition projection2 : pvaluation -> pvaluation
  := [pv : pvaluation] (Build_pvaluation
                          (projection_string (val pv) (shared pv) tokenstring2)
                          (boolprojection_string (shared pv) tokenstring2)).

End PVALJOIN_DEF.*)