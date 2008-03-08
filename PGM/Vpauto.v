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
(*                      Vpauto.v                     *)
(*                     Yijia CHEN                    *)
(*                                                   *)
(*****************************************************)

Require Import PAuto.
Require Import List.  (* for a group of p-automata *)
Require Import Var.
Require Import String.


Set Implicit Arguments.
Unset Strict Implicit.


(*****************************************************)
(*                                                   *)
(*  "vp_auto" defines the type of p_automata that    *)
(*  use the concrete variable valuation of type      *)
(*  "pvaluation".                                    *)
(*                                                   *)
(*****************************************************)

Section VPAUTO_DEF.

Record vp_auto : Type := 
  {Shared_Variables : list string;
   Auto : p_auto pvaluation;
   Is_Critical : string -> Loc Auto -> Prop}.

End VPAUTO_DEF.

(*****************************************************)
(*                                                   *)
(*  "vpauto_sys" is the type of a system of vp_auto. *)
(*  For future use, we must specify the actual index *)
(*  set, more precisely, we must have the capability *)
(*  to enumerate the underlying index set.           *)
(*                                                   *)
(*****************************************************)
Section VPAUTO_SYS_DEF.

Record vpauto_sys : Type := 
  {Index_Domain : Set;
   Index_Set : list Index_Domain;
   Indexed_Pauto : Index_Domain -> vp_auto}.

End VPAUTO_SYS_DEF.



(*****************************************************)
(*                                                   *)
(*  Comparison on Time                               *)
(*                                                   *)
(*****************************************************)

Section TIME_COMPARISON_DEF.

Definition eq_time_typedvalue (s : Time) (tv : typedvalue) :=
  predicate_type1_typedvalue2 (eq (A:=Time)) s tv.

Definition lt_time_typedvalue (s : Time) (tv : typedvalue) :=
  predicate_type1_typedvalue2 Tlt s tv.

Definition le_time_typedvalue (s : Time) (tv : typedvalue) :=
  predicate_type1_typedvalue2 Tle s tv.

Definition gt_time_typedvalue (s : Time) (tv : typedvalue) :=
  predicate_typedvalue1_type2 Tlt tv s.

Definition ge_time_typedvalue (s : Time) (tv : typedvalue) :=
  predicate_typedvalue1_type2 Tle tv s.

End TIME_COMPARISON_DEF.


(*****************************************************)
(*                                                   *)
(*  Urgent Location                                  *)
(*                                                   *)
(*****************************************************)

Section URGENT_DEF.

Variable t : string. (* the local variable to memorize the time upbound *)

Section URGENT_INV_TRANS_DEF.

Variable loc : Set.
Variable act : Set.

Let invariants := loc -> Time -> pvaluation -> Prop.
Let transitions :=
  act -> Time -> loc -> pvaluation -> loc -> pvaluation -> Prop.

Definition urgent_inv (l : loc) (s : Time) (pv : pvaluation) : Prop :=
  eq_time_typedvalue s (pvalue pv t).

Definition is_urgent_inv (inv : invariants) (l : loc) : Prop :=
  forall (pv : pvaluation) (s : Time), inv l s pv -> urgent_inv l s pv.

Definition urgent_trans_in (a : act) (s : Time) (l1 : loc) 
  (pv1 : pvaluation) (l2 : loc) (pv2 : pvaluation) : Prop :=
  eq_time_typedvalue s (pvalue pv2 t).

Definition urgent_trans_out (a : act) (s : Time) (l1 : loc)
  (pv1 : pvaluation) (l2 : loc) (pv2 : pvaluation) : Prop :=
  eq_time_typedvalue s (pvalue pv1 t).

Definition is_urgent_trans (trans : transitions) (l : loc) : Prop :=
  forall (a : act) (s : Time) (l' : loc) (pv1 pv2 : pvaluation),
  trans a s l' pv1 l pv2 ->
  urgent_trans_in a s l' pv1 l pv2 /\
  (forall (a : act) (s : Time) (l' : loc) (pv1 pv2 : pvaluation),
   trans a s l pv1 l' pv2 -> urgent_trans_out a s l pv1 l' pv2).

End URGENT_INV_TRANS_DEF.

Variable vp : vp_auto.

Definition is_urgent (l : Loc (Auto vp)) : Prop :=
  is_urgent_inv (loc:=Loc (Auto vp)) (P_Inv (V:=pvaluation) (p_auto:=Auto vp)) l /\
  is_urgent_trans (loc:=Loc (Auto vp)) (act:=P_Act (Auto vp))
    (P_Trans (V:=pvaluation) (p_auto:=Auto vp)) l.

End URGENT_DEF.


(*****************************************************)
(*                                                   *)
(*  Timer                                            *)
(*                                                   *)
(*****************************************************)

Section TIMER_DEF.

Variable t : string. (* the local variable to memorize the time upbound *)
Variable ivl : Time. (* the time interval *)

Section TIMER_INV_TRANS_DEF.

Variable loc : Set.
Variable act : Set.

Let invariants := loc -> Time -> pvaluation -> Prop.
Let transitions :=
  act -> Time -> loc -> pvaluation -> loc -> pvaluation -> Prop.

Definition timer_inv (l : loc) (s : Time) (pv : pvaluation) : Prop :=
  le_time_typedvalue s (pvalue pv t).

Definition is_timer_inv (inv : invariants) (l : loc) : Prop :=
  forall (pv : pvaluation) (s : Time), inv l s pv -> timer_inv l s pv.

Definition timer_trans_in (a : act) (s : Time) (l1 : loc) 
  (pv1 : pvaluation) (l2 : loc) (pv2 : pvaluation) : Prop :=
  eq_time_typedvalue (s +/ ivl) (pvalue pv2 t).

Definition timer_trans_out (a : act) (s : Time) (l1 : loc) 
  (pv1 : pvaluation) (l2 : loc) (pv2 : pvaluation) : Prop :=
  eq_time_typedvalue s (pvalue pv1 t).

Definition is_timer_trans (trans : transitions) (l : loc) : Prop :=
  forall (a : act) (s : Time) (l' : loc) (pv1 pv2 : pvaluation),
  trans a s l' pv1 l pv2 ->
  timer_trans_in a s l' pv1 l pv2 /\
  (forall (a : act) (s : Time) (l' : loc) (pv1 pv2 : pvaluation),
   trans a s l pv1 l' pv2 -> trans a s l pv1 l' pv2).

End TIMER_INV_TRANS_DEF.

Variable vp : vp_auto.

Definition is_timer (l : Loc (Auto vp)) : Prop :=
  is_timer_inv (loc:=Loc (Auto vp)) (P_Inv (V:=pvaluation) (p_auto:=Auto vp)) l /\
  is_timer_trans (loc:=Loc (Auto vp)) (act:=P_Act (Auto vp))
    (P_Trans (V:=pvaluation) (p_auto:=Auto vp)) l.

End TIMER_DEF.

(*****************************************************)
(*                                                   *)
(*  Case Analysis                                    *)
(*                                                   *)
(*****************************************************)

Section CASE_ANALYSIS_DEF.

Variable t : string. (* the local variable to memorize the time upbound *)

Variable loc : Set.
Variable act : Set.

(* the disjunction of all guards *)

Variable disjunction_of_all_guards : Time -> pvaluation -> Prop.

Definition case_inv (l : loc) (s : Time) (pv : pvaluation) : Prop :=
  forall s' : Time,
  ge_time_typedvalue s' (pvalue pv t) /\ s' <=/ s ->
  ~ disjunction_of_all_guards s' pv.

Definition case_trans_in (a : act) (s : Time) (l1 : loc) 
  (pv1 : pvaluation) (l2 : loc) (pv2 : pvaluation) : Prop :=
  eq_time_typedvalue s (pvalue pv2 t).

Variable guard : Time -> pvaluation -> Prop.

Definition case_trans_out (a : act) (s : Time) (l1 : loc) 
  (pv1 : pvaluation) (l2 : loc) (pv2 : pvaluation) : Prop := 
  guard s pv1.

End CASE_ANALYSIS_DEF.

(*****************************************************)
(*                                                   *)
(*  Shared Variables                                 *)
(*                                                   *)
(*****************************************************)

Section SHARED_VARIABLE_DEF.

Variable vp : vp_auto.
Variable index_domain : Set.
Variable others : list index_domain.

Let sharedvariables := Shared_Variables vp.
Let iscritical := Is_Critical (vp_auto:=vp).


Let loc := Loc (Auto vp).
Let inv := P_Inv (V:=pvaluation) (p_auto:=Auto vp).
Let act := P_Act (Auto vp).

Let trans := P_Trans (V:=pvaluation) (p_auto:=Auto vp).

Definition new_loc := loc.

Definition new_inv := inv.

Inductive new_act : Set :=
  | original : act -> new_act
  | passwriting :
      forall (v : string) (ip : index_domain),
      In v sharedvariables -> In ip others -> new_act.

Inductive new_trans :
new_act -> Time -> new_loc -> pvaluation -> new_loc -> pvaluation -> Prop :=
  | old :
      forall (a : act) (s : Time) (l1 l2 : loc) (pv1 pv2 : pvaluation),
      trans a s l1 pv1 l2 pv2 -> new_trans (original a) s l1 pv1 l2 pv2
  | new :
      forall (v : string) (shared : In v sharedvariables) 
        (ip : index_domain) (other : In ip others) 
        (s : Time) (l : new_loc) (pv1 pv2 : pvaluation),
      ~ iscritical v l ->
      forall v' : string,
      (pvalue pv1 v' <> pvalue pv2 v' -> v = v') ->
      new_trans (passwriting shared other) s l pv1 l pv2.

Definition auto_with_selfloop :=
  Build_p_auto (V:=pvaluation) (Loc:=new_loc) new_inv (P_Act:=new_act)
    new_trans.

Definition all_critical (str : string) (l : new_loc) : Prop := True.

Definition vp_auto_with_selfloop :=
  Build_vp_auto sharedvariables (Auto:=auto_with_selfloop) all_critical.


End SHARED_VARIABLE_DEF.

(*****************************************************)
(*                                                   *)
(*  "channel" specify the type of channels  which    *)
(*  consists of a string (name) and a label from     *)
(*  from the action set.                             *)
(*                                                   *)
(*****************************************************)

Section CHANNEL_DEF.

Variable act : Set.

Record channel : Set :=  {Name : string; Label : act}.


Definition receiver_ready_signal (ch : channel) : string :=
  R :: R :: I :: Name ch.

Definition data_exchange_medium (ch : channel) : string :=
  D :: E :: M :: Name ch.


End CHANNEL_DEF.


(*****************************************************)
(*                                                   *)
(*  Message Passing                                  *)
(*                                                   *)
(*****************************************************)

Section MESSAGE_PASSING_DEF.

Variable t : string. (* local variable used for timer, urgent local, etc. *)

Variable loc : Set.
Variable act : Set.

Let invariants := loc -> Time -> pvaluation -> Prop.
Let transitions :=
  act -> Time -> loc -> pvaluation -> loc -> pvaluation -> Prop.

Variable act_tau : act.
Variable act_writing : string -> act.

Variable ch : channel act.

(*****************************************************)
(*                                                   *)
(*  Sending                                          *)
(*                                                   *)
(*****************************************************)

Section SENDING_DEF.

Variable sending_data : typedvalue.

Variable consume_time : Time.

Let guard_l1 (s : Time) (pv : pvaluation) : Prop :=
  predicate_typedvalue (fun v : bool => v = true)
    (pvalue pv (receiver_ready_signal ch)).

Definition send_inv_l1 (l : loc) (s : Time) (pv : pvaluation) : Prop :=
  case_inv t guard_l1 l s pv.


Definition send_inv_l2 (l : loc) (s : Time) (pv : pvaluation) : Prop :=
  urgent_inv t l s pv.


Definition send_inv_l3 (l : loc) (s : Time) (pv : pvaluation) : Prop :=
  timer_inv t l s pv.

Definition send_trans_l1_in (a : act) (s : Time) (l0 : loc)
  (pv0 : pvaluation) (l1 : loc) (pv1 : pvaluation) : Prop :=
  case_trans_in t a s l0 pv0 l1 pv1.

Definition send_trans_l1_l2 (a : act) (s : Time) (l1 : loc)
  (pv1 : pvaluation) (l2 : loc) (pv2 : pvaluation) : Prop :=
  a = act_writing (data_exchange_medium ch) /\
  case_trans_out guard_l1 a s l1 pv1 l2 pv2 /\
  pvalue pv2 (data_exchange_medium ch) = sending_data /\
  urgent_trans_in t a s l1 pv1 l2 pv2 /\
  eq_pvaluation (prestrict (prestrict pv1 t) (data_exchange_medium ch))
    (prestrict (prestrict pv2 t) (data_exchange_medium ch)).

Definition send_trans_l2_l3 (a : act) (s : Time) (l2 : loc)
  (pv2 : pvaluation) (l3 : loc) (pv3 : pvaluation) : Prop :=
  a = Label ch /\
  timer_trans_in t consume_time a s l2 pv2 l3 pv3 /\
  eq_pvaluation (prestrict pv2 t) (prestrict pv3 t).

Definition send_trans_l3_out (a : act) (s : Time) (l3 : loc)
  (pv3 : pvaluation) (l4 : loc) (pv4 : pvaluation) : Prop :=
  timer_trans_out t a s l3 pv3 l4 pv4.

Definition send_is_critical_l2 (str : string) (l2 l : loc) : Prop :=
  str = data_exchange_medium ch /\ l = l2.

End SENDING_DEF.


(*****************************************************)
(*                                                   *)
(*  Receiving                                        *)
(*                                                   *)
(*****************************************************)

Section RECEIVING_DEF.

Variable receiver_variable : string.

Variable consume_time : Time.

Definition receive_inv_l1 (l : loc) (s : Time) (pv : pvaluation) : Prop :=
  urgent_inv t l s pv.

Definition receive_inv_l2 (l : loc) (s : Time) (pv : pvaluation) : Prop :=
  True.

Definition receive_inv_l3 (l : loc) (s : Time) (pv : pvaluation) : Prop :=
  urgent_inv t l s pv.

Definition receive_inv_l4 (l : loc) (s : Time) (pv : pvaluation) : Prop :=
  timer_inv t l s pv.

Definition receive_trans_l1_in (a : act) (s : Time) 
  (l0 : loc) (pv0 : pvaluation) (l1 : loc) (pv1 : pvaluation) : Prop :=
  urgent_trans_in t a s l0 pv0 l1 pv1.

Definition receive_trans_l1_l2 (a : act) (s : Time) 
  (l1 : loc) (pv1 : pvaluation) (l2 : loc) (pv2 : pvaluation) : Prop :=
  a = act_writing (receiver_ready_signal ch) /\
  urgent_trans_out t a s l1 pv1 l2 pv2 /\
  pvalue pv2 (receiver_ready_signal ch) = Build_typedvalue true /\
  eq_pvaluation pv1 pv2.


(*****************************************************)
(*                                                   *)
(*  Note there is no need to specify the selfloop    *)
(*  on l2 with lable indicating some passive update  *)
(*  of data_exchange_medium, since it will be        *)
(*  generated auotmatically by the process of the    *)
(*  module "Shared Variables".                       *)
(*                                                   *)
(*****************************************************)


Definition receive_trans_l2_l3 (a : act) (s : Time) 
  (l2 : loc) (pv2 : pvaluation) (l3 : loc) (pv3 : pvaluation) : Prop :=
  a = Label ch /\
  urgent_trans_in t a s l2 pv2 l3 pv3 /\
  pvalue pv3 receiver_variable = pvalue pv2 (data_exchange_medium ch) /\
  eq_pvaluation (prestrict (prestrict pv2 t) receiver_variable)
    (prestrict (prestrict pv3 t) receiver_variable).

Definition receive_trans_l3_l4 (a : act) (s : Time) 
  (l3 : loc) (pv3 : pvaluation) (l4 : loc) (pv4 : pvaluation) : Prop :=
  a = act_writing (receiver_ready_signal ch) /\
  urgent_trans_out t a s l3 pv3 l4 pv4 /\
  timer_trans_in t consume_time a s l3 pv3 l4 pv4 /\
  pvalue pv4 (receiver_ready_signal ch) = Build_typedvalue false /\
  eq_pvaluation (prestrict (prestrict pv3 t) (receiver_ready_signal ch))
    (prestrict (prestrict pv4 t) (receiver_ready_signal ch)).

Definition receive_trans_l4_out (a : act) (s : Time) 
  (l4 : loc) (pv4 : pvaluation) (l5 : loc) (pv5 : pvaluation) : Prop :=
  timer_trans_out t a s l4 pv4 l5 pv5.


End RECEIVING_DEF.


End MESSAGE_PASSING_DEF.


(*****************************************************)
(*                                                   *)
(*  renaming of transition labels                    *)
(*                                                   *)
(*****************************************************)

Section RENAME_LABEL_DEF.

Variable vp : vp_auto.

Let sharedvariables := Shared_Variables vp.
Let iscritical := Is_Critical (vp_auto:=vp).

Let loc := Loc (Auto vp).
Let inv := P_Inv (V:=pvaluation) (p_auto:=Auto vp).
Let act := P_Act (Auto vp).
Let trans := P_Trans (V:=pvaluation) (p_auto:=Auto vp).

Variable newact : Set.
Variable projnaming : newact -> act.

Let newtrans (a : newact) (s : Time) (l1 : loc) (pv1 : pvaluation) 
  (l2 : loc) (pv2 : pvaluation) : Prop :=
  trans (projnaming a) s l1 pv1 l2 pv2.

End RENAME_LABEL_DEF.

(*****************************************************)
(*                                                   *)
(*  sychronise product of two vp_automata            *)
(*                                                   *)
(*****************************************************)
(*
Section PRODUCT_VPAUTO_DEF.

Variables vp1, vp2 : vp_auto.

Variable Syncvect : (!Actsync pvaluation pvaluation vp1 vp2) -> Prop.

Definition VPauto_sync : vp_auto :=
 (!Pauto_sync pvaluation pvaluation vp1 vp2 Syncvect
    pvaluation projection1 projection2).

End PRODUCT_VPAUTO_DEF.
*)