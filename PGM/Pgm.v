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
(*                        Pgm.v                      *)
(*                     Yijia CHEN                    *)
(*                                                   *)
(*****************************************************)

Require Import PAuto.
Require Import Queue.
Require Import List.
Require Import String.

Require Import Var.
Require Import Vpauto.


Set Implicit Arguments.
Unset Strict Implicit.


(*****************************************************)
(*                                                   *)
(*  "MESSAGE_PASSING_TIME" defines the time required *)
(*  to finish a message passing session. In practice *)
(*  it may vary depends on the amount of data, but   *)
(*  here for simplicity we fix it as a parameter.    *) 
(*                                                   *)
(*****************************************************)

Local Parameter MESSAGE_PASSING_TIME : Time. 

Inductive MESSAGE : Set :=
  | SPM : nat -> nat -> MESSAGE (* SPM   (trail, lead) *)
  | ODATA : nat -> nat -> MESSAGE (* ODATA (trail, sqn)  *)
  | RDATA : nat -> nat -> MESSAGE (* RDATA (trail, sqn)  *)
  | NAK : nat -> MESSAGE (* NAK   (sqn)         *)
  | NCF : nat -> MESSAGE (* NCF   (sqn)         *)
  | ERRMSG : MESSAGE.              (* ERROR message       *)

Definition is_spm (m : MESSAGE) : Prop :=
  match m with
  | SPM _ _ => True
  | _ => False
  end.

Definition is_odata (m : MESSAGE) : Prop :=
  match m with
  | ODATA _ _ => True
  | _ => False
  end.

Definition is_rdata (m : MESSAGE) : Prop :=
  match m with
  | RDATA _ _ => True
  | _ => False
  end.

Definition is_nak (m : MESSAGE) : Prop :=
  match m with
  | NAK _ => True
  | _ => False
  end.

Definition is_ncf (m : MESSAGE) : Prop :=
  match m with
  | NCF _ => True
  | _ => False
  end.

(*****************************************************)
(*                                                   *)
(*  Environment                                      *)
(*                                                   *)
(*****************************************************)

Local Parameter DATA_RPT_RTE : Time.

Section ENVIORNMENT_DEF.

Let sharedvariables : list string := nil.

Inductive EnvLoc : Set :=
  | EnvLoc1 : EnvLoc
  | EnvLoc2 : EnvLoc
  | EnvLoc3 : EnvLoc.

Inductive EnvAct : Set :=
  | EnvActData : EnvAct
  | EnvActTau : EnvAct.

Let transitions :=
  EnvAct -> Time -> EnvLoc -> pvaluation -> EnvLoc -> pvaluation -> Prop.

Let invariants := EnvLoc -> Time -> pvaluation -> Prop.

Let t : string := T :: voidstring.
Let t1 : string := T :: t.

Let inv : invariants :=
  fun (l : EnvLoc) (s : Time) (pv : pvaluation) =>
  is_type pv t Time /\
  is_type pv t1 Time /\
  match l with
  | EnvLoc1 => urgent_inv t l s pv
  | EnvLoc2 => True
  | EnvLoc3 => timer_inv t l s pv
  end.

Let L1_L2 (a : EnvAct) (s : Time) (pv1 pv2 : pvaluation) : Prop :=
  a = EnvActTau /\
  urgent_trans_out t a s EnvLoc1 pv1 EnvLoc2 pv2 /\
  eq_time_typedvalue (s +/ DATA_RPT_RTE) (pvalue pv2 t1) /\
  eq_pvaluation (prestrict (prestrict pv1 t) t1)
    (prestrict (prestrict pv2 t) t1).

Let L2_L3 (a : EnvAct) (s : Time) (pv2 pv3 : pvaluation) : Prop :=
  a = EnvActData /\
  ge_time_typedvalue s (pvalue pv2 t1) /\
  timer_trans_in t MESSAGE_PASSING_TIME a s EnvLoc2 pv2 EnvLoc3 pv3 /\
  eq_pvaluation (prestrict pv2 t) (prestrict pv3 t).

Let L3_L2 (a : EnvAct) (s : Time) (pv3 pv2 : pvaluation) : Prop :=
  a = EnvActTau /\
  eq_time_typedvalue (s +/ DATA_RPT_RTE) (pvalue pv2 t1) /\
  eq_pvaluation (prestrict (prestrict pv3 t) t1)
    (prestrict (prestrict pv2 t) t1).


Let trans : transitions :=
  fun (a : EnvAct) (s : Time) (l1 : EnvLoc) (pv1 : pvaluation) 
    (l2 : EnvLoc) (pv2 : pvaluation) =>
  match l1, l2 with
  | EnvLoc1, EnvLoc2 => L1_L2 a s pv1 pv2
  | EnvLoc2, EnvLoc3 => L2_L3 a s pv1 pv2
  | EnvLoc3, EnvLoc2 => L3_L2 a s pv1 pv2
  | _, _ => False
  end.

Let is_critical (str : string) (l : EnvLoc) : Prop := False.

Definition Env : vp_auto :=
  Build_vp_auto sharedvariables (Auto:=Build_p_auto inv trans) is_critical.

End ENVIORNMENT_DEF.

(*****************************************************)
(*                                                   *)
(*  Source                                           *)
(*                                                   *)
(*****************************************************)

Section SOURCE_DEF.

(*****************************************************)
(*                                                   *)
(*  Shared Variables and Channels                    *)
(*                                                   *)
(*****************************************************)


(*****************************************************)
(*  the variables defining the trailing and leading  *)
(*  edge of the transmit window                      *)
(*                                                   *)

Variable txw_trail txw_lead : string.

(*                                                   *)
(*****************************************************)

(*****************************************************)
(*  a bounded priority queue buffering outgoing      *)
(*  SPM, ODATA, RDATA and NCF                        *)
(*                                                   *)

Variable que_msg : string.

(*  NCF > SPM > ODATA, RDATA                         *)

Let weight_que_msg (msg : MESSAGE) : nat :=
  match msg with
  | NCF _ => 2
  | SPM _ _ => 1
  | _ => 0
  end.

Let MESSAGE_QUEUE := Queue MESSAGE.

Let pop_ele_que_msg (q : MESSAGE_QUEUE) := pop_ele ERRMSG weight_que_msg q.

Let pop_que_que_msg (q : MESSAGE_QUEUE) := pop_que ERRMSG weight_que_msg q.

(*                                                   *)
(*****************************************************)


(*****************************************************)
(*  a queue buffering RDATA that are waiting for     *)
(*  actual transmission                              *)
(*                                                   *)

Variable que_loss : string.

(*  Each entry of the queue is a tuple [sqn, t]      *)

Record WAITING_RDATA : Set :=  {sqn : nat; time : Time}.


Let ERRWAITINGRDATA := Build_WAITING_RDATA 0 T0. 

(* so the time of the whole system starts from > 0   *)
(* or the sequence number of any data != 0,          *)
(* since [0, 0] is resevered to represent an error   *)
(* waiting RDATA                                     *)


Let weight_que_loss (wr : WAITING_RDATA) : nat := 0.

Let WAITING_RDATA_QUEUE := Queue WAITING_RDATA.

Let pop_ele_que_loss (q : WAITING_RDATA_QUEUE) :=
  pop_ele ERRWAITINGRDATA weight_que_loss q.

Let pop_que_que_loss (q : WAITING_RDATA_QUEUE) :=
  pop_que ERRWAITINGRDATA weight_que_loss q.


(*                                                   *)
(*****************************************************)




Variable ch_in ch_out : string.

(*****************************************************)
(*                                                   *)
(*  Ambient SPM Generation                           *)
(*                                                   *)
(*****************************************************)

Variable SPM_RPT_RTE : Time.

Section SOURCE_AMBIENT_SPM_GENERATION_DEF.

Let sharedvariables : list string := txw_trail :: txw_lead :: que_msg :: nil.

Inductive SouAmbSpmGenLoc : Set :=
  | SouAmbSpmGenLoc1 : SouAmbSpmGenLoc
  | SouAmbSpmGenLoc2 : SouAmbSpmGenLoc
  | SouAmbSpmGenLoc3 : SouAmbSpmGenLoc.

Inductive SouAmbSpmGenAct : Set :=
  | SouAmbSpmGenActTau : SouAmbSpmGenAct
  | SouAmbSpmGenActWrite : string -> SouAmbSpmGenAct.

Let transitions :=
  SouAmbSpmGenAct ->
  Time ->
  SouAmbSpmGenLoc -> pvaluation -> SouAmbSpmGenLoc -> pvaluation -> Prop.

Let invariants := SouAmbSpmGenLoc -> Time -> pvaluation -> Prop.

Let t : string := T :: voidstring.
Let t1 : string := T :: t.

Let inv : invariants :=
  fun (l : SouAmbSpmGenLoc) (s : Time) (pv : pvaluation) =>
  is_type pv t Time /\
  is_type pv t1 Time /\
  is_type pv que_msg MESSAGE_QUEUE /\
  is_type pv txw_lead nat /\
  is_type pv txw_trail nat /\
  match l with
  | SouAmbSpmGenLoc1 => urgent_inv t l s pv
  | SouAmbSpmGenLoc2 => le_time_typedvalue s (pvalue pv t1)
  | SouAmbSpmGenLoc3 => urgent_inv t l s pv
  end.

Let L1_L2 (a : SouAmbSpmGenAct) (s : Time) (pv1 pv2 : pvaluation) : Prop :=
  a = SouAmbSpmGenActTau /\
  urgent_trans_out t a s SouAmbSpmGenLoc1 pv1 SouAmbSpmGenLoc2 pv2 /\
  eq_time_typedvalue (s +/ SPM_RPT_RTE) (pvalue pv2 t1) /\
  eq_pvaluation (prestrict (prestrict pv1 t) t1)
    (prestrict (prestrict pv2 t) t1).


Let push_spm (trail lead : nat) (q1 q2 : MESSAGE_QUEUE) :=
  q2 = push (SPM trail lead) q1.

Let L2_L3 (a : SouAmbSpmGenAct) (s : Time) (pv2 pv3 : pvaluation) : Prop :=
  a = SouAmbSpmGenActWrite que_msg /\
  eq_time_typedvalue s (pvalue pv2 t1) /\
  urgent_trans_in t a s SouAmbSpmGenLoc2 pv2 SouAmbSpmGenLoc3 pv3 /\
  (forall trail lead : nat,
   pvalue pv2 txw_trail = Build_typedvalue trail ->
   pvalue pv2 txw_lead = Build_typedvalue lead ->
   predicate_typedvalue1_typedvalue2 (push_spm trail lead)
     (pvalue pv2 que_msg) (pvalue pv3 que_msg)) /\
  eq_pvaluation (prestrict (prestrict pv2 t) que_msg)
    (prestrict (prestrict pv3 t) que_msg).

Let L3_L2 (a : SouAmbSpmGenAct) (s : Time) (pv3 pv2 : pvaluation) : Prop :=
  a = SouAmbSpmGenActTau /\
  urgent_trans_out t a s SouAmbSpmGenLoc3 pv3 SouAmbSpmGenLoc2 pv2 /\
  eq_time_typedvalue (s +/ SPM_RPT_RTE) (pvalue pv2 t1) /\
  eq_pvaluation (prestrict (prestrict pv3 t) t1)
    (prestrict (prestrict pv2 t) t1).

Let trans : transitions :=
  fun (a : SouAmbSpmGenAct) (s : Time) (l1 : SouAmbSpmGenLoc)
    (pv1 : pvaluation) (l2 : SouAmbSpmGenLoc) (pv2 : pvaluation) =>
  match l1, l2 with
  | SouAmbSpmGenLoc1, SouAmbSpmGenLoc2 => L1_L2 a s pv1 pv2
  | SouAmbSpmGenLoc2, SouAmbSpmGenLoc3 => L2_L3 a s pv1 pv2
  | SouAmbSpmGenLoc3, SouAmbSpmGenLoc2 => L3_L2 a s pv1 pv2
  | _, _ => False
  end.

Let is_critical (str : string) (l : SouAmbSpmGenLoc) : Prop :=
  str = que_msg /\ l = SouAmbSpmGenLoc3.

Definition SouAmbSpmGen : vp_auto :=
  Build_vp_auto sharedvariables (Auto:=Build_p_auto inv trans) is_critical.

End SOURCE_AMBIENT_SPM_GENERATION_DEF.


(*****************************************************)
(*                                                   *)
(*  Heartbeat SPM Generation                         *)
(*                                                   *)
(*****************************************************)

Variable IHB_MIN IHB_MAX : Time.

Section SOURCE_HEARTBEAT_SPM_GENERATION_DEF.

Let sharedvariables : list string := txw_trail :: txw_lead :: que_msg :: nil.

Inductive SouHeaSpmGenLoc : Set :=
  | SouHeaSpmGenLoc1 : SouHeaSpmGenLoc
  | SouHeaSpmGenLoc2 : SouHeaSpmGenLoc
  | SouHeaSpmGenLoc3 : SouHeaSpmGenLoc.

Inductive SouHeaSpmGenAct : Set :=
  | SouHeaSpmGenActTau : SouHeaSpmGenAct
  | SouHeaSpmGenActWrite : string -> SouHeaSpmGenAct.


Let transitions :=
  SouHeaSpmGenAct ->
  Time ->
  SouHeaSpmGenLoc -> pvaluation -> SouHeaSpmGenLoc -> pvaluation -> Prop.

Let invariants := SouHeaSpmGenLoc -> Time -> pvaluation -> Prop.

Let t : string := T :: voidstring.
Let t1 : string := T :: t.

Let ivl : string := I :: V :: L :: voidstring.

Fixpoint que_msg_has_data (q : MESSAGE_QUEUE) : Prop :=
  match q with
  | empty => False
  | push msg q' =>
      match msg with
      | ODATA _ _ => True
      | RDATA _ _ => True
      | _ => que_msg_has_data q'
      end
  end.

Let guard_L1 (s : Time) (pv : pvaluation) : Prop :=
  predicate_typedvalue (fun q : MESSAGE_QUEUE => ~ que_msg_has_data q)
    (pvalue pv que_msg).


Let guard_L2_1 (s : Time) (pv : pvaluation) : Prop :=
  eq_time_typedvalue s (pvalue pv t1).

Let guard_L2_2 (s : Time) (pv : pvaluation) : Prop :=
  predicate_typedvalue que_msg_has_data (pvalue pv que_msg).


Let guard_L2 (s : Time) (pv : pvaluation) :=
  guard_L2_1 s pv \/ guard_L2_2 s pv.

Let inv : invariants :=
  fun (l : SouHeaSpmGenLoc) (s : Time) (pv : pvaluation) =>
  is_type pv t Time /\
  is_type pv t1 Time /\
  is_type pv ivl Time /\
  is_type pv que_msg MESSAGE_QUEUE /\
  is_type pv txw_lead nat /\
  is_type pv txw_trail nat /\
  match l with
  | SouHeaSpmGenLoc1 => case_inv t guard_L1 l s pv
  | SouHeaSpmGenLoc2 => case_inv t guard_L2 l s pv
  | SouHeaSpmGenLoc3 => urgent_inv t l s pv
  end.

Let L1_L2 (a : SouHeaSpmGenAct) (s : Time) (pv1 pv2 : pvaluation) : Prop :=
  a = SouHeaSpmGenActTau /\
  case_trans_out guard_L1 a s SouHeaSpmGenLoc1 pv1 SouHeaSpmGenLoc2 pv2 /\
  case_trans_in t a s SouHeaSpmGenLoc1 pv1 SouHeaSpmGenLoc2 pv2 /\
  eq_time_typedvalue IHB_MIN (pvalue pv2 ivl) /\
  eq_time_typedvalue (s +/ IHB_MIN) (pvalue pv2 t1) /\
  eq_pvaluation (prestrict pv1 t) (prestrict pv2 t).


Let push_spm (trail lead : nat) (q1 q2 : MESSAGE_QUEUE) :=
  q2 = push (SPM trail lead) q1.

Let L2_L3 (a : SouHeaSpmGenAct) (s : Time) (pv2 pv3 : pvaluation) : Prop :=
  a = SouHeaSpmGenActWrite que_msg /\
  case_trans_out guard_L2_1 a s SouHeaSpmGenLoc2 pv2 SouHeaSpmGenLoc3 pv3 /\
  urgent_trans_in t a s SouHeaSpmGenLoc2 pv2 SouHeaSpmGenLoc3 pv3 /\
  (forall trail lead : nat,
   pvalue pv2 txw_trail = Build_typedvalue trail ->
   pvalue pv2 txw_lead = Build_typedvalue lead ->
   predicate_typedvalue1_typedvalue2 (push_spm trail lead)
     (pvalue pv2 que_msg) (pvalue pv3 que_msg)) /\
  eq_pvaluation (prestrict (prestrict pv2 t) que_msg)
    (prestrict (prestrict pv3 t) que_msg).

Let newivl_eq_min_of_two_times_of_ivl_and_ihb_max (newivl ivl : Time) :=
  let twoivl := ivl +/ ivl in
  (newivl = twoivl \/ newivl = IHB_MAX) /\
  newivl <=/ twoivl /\ newivl <=/ IHB_MAX.

Let t_eq_s_plus_ivl (t1 s ivl : Time) := t1 = s +/ ivl.

Let L3_L2 (a : SouHeaSpmGenAct) (s : Time) (pv3 pv2 : pvaluation) : Prop :=
  a = SouHeaSpmGenActTau /\
  urgent_trans_out t a s SouHeaSpmGenLoc3 pv3 SouHeaSpmGenLoc2 pv2 /\
  case_trans_in t a s SouHeaSpmGenLoc3 pv3 SouHeaSpmGenLoc2 pv2 /\
  predicate_typedvalue1_typedvalue2
    newivl_eq_min_of_two_times_of_ivl_and_ihb_max (pvalue pv3 ivl)
    (pvalue pv2 ivl) /\
  predicate_typedvalue1_typedvalue2
    (fun t1 ivl : Time => t_eq_s_plus_ivl t1 s ivl) 
    (pvalue pv3 ivl) (pvalue pv2 t1) /\
  eq_pvaluation (prestrict (prestrict pv3 t) t1)
    (prestrict (prestrict pv2 t) t1).

Let L2_L1 (a : SouHeaSpmGenAct) (s : Time) (pv2 pv1 : pvaluation) : Prop :=
  a = SouHeaSpmGenActTau /\
  case_trans_out guard_L2_2 a s SouHeaSpmGenLoc2 pv2 SouHeaSpmGenLoc1 pv1 /\
  case_trans_in t a s SouHeaSpmGenLoc2 pv2 SouHeaSpmGenLoc1 pv1 /\
  eq_pvaluation (prestrict pv2 t) (prestrict pv1 t).


Let trans : transitions :=
  fun (a : SouHeaSpmGenAct) (s : Time) (l1 : SouHeaSpmGenLoc)
    (pv1 : pvaluation) (l2 : SouHeaSpmGenLoc) (pv2 : pvaluation) =>
  match l1, l2 with
  | SouHeaSpmGenLoc1, SouHeaSpmGenLoc2 => L1_L2 a s pv1 pv2
  | SouHeaSpmGenLoc2, SouHeaSpmGenLoc3 => L2_L3 a s pv1 pv2
  | SouHeaSpmGenLoc3, SouHeaSpmGenLoc2 => L3_L2 a s pv1 pv2
  | SouHeaSpmGenLoc2, SouHeaSpmGenLoc1 => L2_L1 a s pv1 pv2
  | _, _ => False
  end.

Let is_critical (str : string) (l : SouHeaSpmGenLoc) : Prop :=
  str = que_msg /\ l = SouHeaSpmGenLoc3.

Definition SouHeaSpmGen : vp_auto :=
  Build_vp_auto sharedvariables (Auto:=Build_p_auto inv trans) is_critical.

End SOURCE_HEARTBEAT_SPM_GENERATION_DEF.

(*****************************************************)
(*                                                   *)
(*  ODATA Generation                                 *)
(*                                                   *)
(*****************************************************)

Section SOURCE_ODATA_GENERATION_DEF.

Let sharedvariables : list string := txw_trail :: txw_lead :: que_msg :: nil.

Inductive SouOdaGenLoc : Set :=
  | SouOdaGenLoc1 : SouOdaGenLoc
  | SouOdaGenLoc2 : SouOdaGenLoc
  | SouOdaGenLoc3 : SouOdaGenLoc.

Inductive SouOdaGenAct : Set :=
  | SouOdaGenActTau : SouOdaGenAct (* not used but kept for furture *)
  | SouOdaGenActData : SouOdaGenAct
  | SouOdaGenActWrite : string -> SouOdaGenAct.

Let transitions :=
  SouOdaGenAct ->
  Time -> SouOdaGenLoc -> pvaluation -> SouOdaGenLoc -> pvaluation -> Prop.

Let invariants := SouOdaGenLoc -> Time -> pvaluation -> Prop.

Let t : string := T :: voidstring.

Let inv : invariants :=
  fun (l : SouOdaGenLoc) (s : Time) (pv : pvaluation) =>
  is_type pv t Time /\
  is_type pv que_msg MESSAGE_QUEUE /\
  is_type pv txw_lead nat /\
  is_type pv txw_trail nat /\
  match l with
  | SouOdaGenLoc1 => True
  | SouOdaGenLoc2 => timer_inv t l s pv
  | SouOdaGenLoc3 => urgent_inv t l s pv
  end.

Let L1_L2 (a : SouOdaGenAct) (s : Time) (pv1 pv2 : pvaluation) : Prop :=
  a = SouOdaGenActData /\
  timer_trans_in t MESSAGE_PASSING_TIME a s SouOdaGenLoc1 pv1 SouOdaGenLoc2
    pv2 /\ eq_pvaluation (prestrict pv1 t) (prestrict pv2 t).

Let L2_L3 (a : SouOdaGenAct) (s : Time) (pv2 pv3 : pvaluation) : Prop :=
  a = SouOdaGenActWrite txw_lead /\
  timer_trans_out t a s SouOdaGenLoc2 pv2 SouOdaGenLoc3 pv3 /\
  urgent_trans_in t a s SouOdaGenLoc2 pv2 SouOdaGenLoc3 pv3 /\
  predicate_typedvalue1_typedvalue2 (fun n1 n2 : nat => n2 = S n1)
    (pvalue pv2 txw_lead) (pvalue pv3 txw_lead) /\
  eq_pvaluation (prestrict (prestrict pv2 t) txw_lead)
    (prestrict (prestrict pv3 t) txw_lead).

Let push_odata (trail lead : nat) (q1 q2 : MESSAGE_QUEUE) :=
  q2 = push (ODATA trail lead) q1.

Let L3_L1 (a : SouOdaGenAct) (s : Time) (pv3 pv1 : pvaluation) : Prop :=
  a = SouOdaGenActWrite que_msg /\
  urgent_trans_out t a s SouOdaGenLoc3 pv3 SouOdaGenLoc1 pv1 /\
  (forall trail lead : nat,
   pvalue pv3 txw_trail = Build_typedvalue trail ->
   pvalue pv3 txw_lead = Build_typedvalue lead ->
   predicate_typedvalue1_typedvalue2 (push_odata trail lead)
     (pvalue pv3 que_msg) (pvalue pv1 que_msg)) /\
  eq_pvaluation (prestrict (prestrict pv3 t) que_msg)
    (prestrict (prestrict pv1 t) que_msg).

Let trans : transitions :=
  fun (a : SouOdaGenAct) (s : Time) (l1 : SouOdaGenLoc) 
    (pv1 : pvaluation) (l2 : SouOdaGenLoc) (pv2 : pvaluation) =>
  match l1, l2 with
  | SouOdaGenLoc1, SouOdaGenLoc2 => L1_L2 a s pv1 pv2
  | SouOdaGenLoc2, SouOdaGenLoc3 => L2_L3 a s pv1 pv2
  | SouOdaGenLoc3, SouOdaGenLoc1 => L3_L1 a s pv1 pv2
  | _, _ => False
  end.

Let is_critical (str : string) (l : SouOdaGenLoc) : Prop :=
  str = txw_lead /\ l = SouOdaGenLoc3.

Definition SouOdaGen : vp_auto :=
  Build_vp_auto sharedvariables (Auto:=Build_p_auto inv trans) is_critical.

End SOURCE_ODATA_GENERATION_DEF.


(*****************************************************)
(*                                                   *)
(*  NAK Processing                                   *)
(*                                                   *)
(*****************************************************)

Variable RDATA_DELAY_IVL : Time.

Section SOURCE_NAK_PROCESSING_DEF.

Let sharedvariables : list string :=
  txw_trail :: txw_lead :: que_loss :: que_msg :: nil.

Inductive SouNakProLoc : Set :=
  | SouNakProLoc1 : SouNakProLoc
  | SouNakProLoc2 : SouNakProLoc
  | SouNakProLoc3 : SouNakProLoc
  | SouNakProLoc4 : SouNakProLoc
  | SouNakProLoc5 : SouNakProLoc.

Inductive SouNakProAct : Set :=
  | SouNakProActTau : SouNakProAct
  | SouNakProActChIn : SouNakProAct
  | SouNakProActWrite : string -> SouNakProAct.

Let transitions :=
  SouNakProAct ->
  Time -> SouNakProLoc -> pvaluation -> SouNakProLoc -> pvaluation -> Prop.

Let invariants := SouNakProLoc -> Time -> pvaluation -> Prop.

Let t : string := T :: voidstring.

Let d : string := D :: voidstring.

Let SouNakPro_ch_in := Build_channel ch_in SouNakProActChIn.

Let inv : invariants :=
  fun (l : SouNakProLoc) (s : Time) (pv : pvaluation) =>
  is_type pv t Time /\
  is_type pv d MESSAGE /\
  is_type pv que_msg MESSAGE_QUEUE /\
  is_type pv que_loss WAITING_RDATA_QUEUE /\
  is_type pv txw_lead nat /\
  is_type pv txw_trail nat /\
  match l with
  | SouNakProLoc1 => receive_inv_l1 t l s pv
  | SouNakProLoc2 => receive_inv_l2 l s pv
  | SouNakProLoc3 => receive_inv_l3 t l s pv
  | SouNakProLoc4 => receive_inv_l4 t l s pv
  | SouNakProLoc5 => urgent_inv t l s pv
  end.

Let L1_L2 (a : SouNakProAct) (s : Time) (pv1 pv2 : pvaluation) : Prop :=
  receive_trans_l1_l2 t SouNakProActWrite SouNakPro_ch_in a s SouNakProLoc1
    pv1 SouNakProLoc2 pv2.


Let L2_L3 (a : SouNakProAct) (s : Time) (pv2 pv3 : pvaluation) : Prop :=
  receive_trans_l2_l3 t SouNakPro_ch_in d a s SouNakProLoc2 pv2 SouNakProLoc3
    pv3.

Let L3_L4 (a : SouNakProAct) (s : Time) (pv3 pv4 : pvaluation) : Prop :=
  receive_trans_l3_l4 t SouNakProActWrite SouNakPro_ch_in
    MESSAGE_PASSING_TIME a s SouNakProLoc3 pv3 SouNakProLoc4 pv4.

Let L4_L1 (a : SouNakProAct) (s : Time) (pv4 pv1 : pvaluation) : Prop :=
  receive_trans_l4_out t a s SouNakProLoc4 pv4 SouNakProLoc1 pv1 /\
  receive_trans_l1_in t a s SouNakProLoc4 pv4 SouNakProLoc1 pv1 /\
  predicate_typedvalue (fun m : MESSAGE => ~ is_nak m) (pvalue pv4 d) /\
  eq_pvaluation (prestrict pv4 t) (prestrict pv1 t).

Let push_ncf (sqn : nat) (q1 q2 : MESSAGE_QUEUE) := q2 = push (NCF sqn) q1.

Let L4_L5 (a : SouNakProAct) (s : Time) (pv4 pv5 : pvaluation) : Prop :=
  a = SouNakProActWrite que_msg /\
  receive_trans_l4_out t a s SouNakProLoc4 pv4 SouNakProLoc5 pv5 /\
  urgent_trans_in t a s SouNakProLoc4 pv4 SouNakProLoc5 pv5 /\
  predicate_typedvalue is_nak (pvalue pv4 d) /\
  (forall sqn : nat,
   pvalue pv4 d = Build_typedvalue (NAK sqn) ->
   predicate_typedvalue1_typedvalue2 (push_ncf sqn) 
     (pvalue pv4 que_msg) (pvalue pv5 que_msg)) /\
  eq_pvaluation (prestrict (prestrict pv4 t) que_msg)
    (prestrict (prestrict pv5 t) que_msg).

Let sqn_in_txw (sqn trail lead : nat) : Prop := trail <= sqn /\ sqn <= lead.

Let L5_L1_1 (a : SouNakProAct) (s : Time) (pv5 pv1 : pvaluation) : Prop :=
  a = SouNakProActTau /\
  urgent_trans_out t a s SouNakProLoc5 pv5 SouNakProLoc1 pv1 /\
  receive_trans_l1_in t a s SouNakProLoc5 pv5 SouNakProLoc1 pv1 /\
  (forall sqn : nat,
   pvalue pv5 d = Build_typedvalue (NAK sqn) ->
   predicate_typedvalue1_typedvalue2
     (fun trail lead : nat => ~ sqn_in_txw sqn trail lead)
     (pvalue pv5 txw_trail) (pvalue pv5 txw_lead)) /\
  eq_pvaluation (prestrict pv5 t) (prestrict pv1 t).


Let push_waiting_rdata (sqn : nat) (time : Time)
  (q1 q2 : WAITING_RDATA_QUEUE) :=
  q2 = push (Build_WAITING_RDATA sqn time) q1.

Let L5_L1_2 (a : SouNakProAct) (s : Time) (pv5 pv1 : pvaluation) : Prop :=
  a = SouNakProActWrite que_msg /\
  urgent_trans_out t a s SouNakProLoc5 pv5 SouNakProLoc1 pv1 /\
  receive_trans_l1_in t a s SouNakProLoc5 pv5 SouNakProLoc1 pv1 /\
  (forall sqn : nat,
   pvalue pv5 d = Build_typedvalue (NAK sqn) ->
   predicate_typedvalue1_typedvalue2 (sqn_in_txw sqn) 
     (pvalue pv5 txw_trail) (pvalue pv5 txw_lead) /\
   predicate_typedvalue1_typedvalue2
     (push_waiting_rdata sqn (s +/ RDATA_DELAY_IVL)) 
     (pvalue pv5 que_loss) (pvalue pv1 que_loss)) /\
  eq_pvaluation (prestrict (prestrict pv5 t) que_loss)
    (prestrict (prestrict pv1 t) que_loss).

Let L5_L1 (a : SouNakProAct) (s : Time) (pv5 pv1 : pvaluation) : Prop :=
  L5_L1_1 a s pv5 pv1 \/ L5_L1_2 a s pv5 pv1.


Let trans : transitions :=
  fun (a : SouNakProAct) (s : Time) (l1 : SouNakProLoc) 
    (pv1 : pvaluation) (l2 : SouNakProLoc) (pv2 : pvaluation) =>
  match l1, l2 with
  | SouNakProLoc1, SouNakProLoc2 => L1_L2 a s pv1 pv2
  | SouNakProLoc2, SouNakProLoc3 => L2_L3 a s pv1 pv2
  | SouNakProLoc3, SouNakProLoc4 => L3_L4 a s pv1 pv2
  | SouNakProLoc4, SouNakProLoc5 => L4_L5 a s pv1 pv2
  | SouNakProLoc5, SouNakProLoc1 => L5_L1 a s pv1 pv2
  | _, _ => False
  end.

Let is_critical (str : string) (l : SouNakProLoc) : Prop :=
  str = d /\ l = SouNakProLoc3.

Definition SouNakProGen : vp_auto :=
  Build_vp_auto sharedvariables (Auto:=Build_p_auto inv trans) is_critical.

End SOURCE_NAK_PROCESSING_DEF.


(*****************************************************)
(*                                                   *)
(*  RDATA Generation                                 *)
(*                                                   *)
(*****************************************************)

Section SOURCE_RDATA_GENERATION_DEF.

Let sharedvariables : list string := txw_trail :: que_loss :: que_msg :: nil.

Inductive SouRdaGenLoc : Set :=
  | SouRdaGenLoc1 : SouRdaGenLoc
  | SouRdaGenLoc2 : SouRdaGenLoc.

Inductive SouRdaGenAct : Set :=
  | SouRdaGenActTau : SouRdaGenAct (* not used but kept for furture *)
  | SouRdaGenActWrite : string -> SouRdaGenAct.

Let transitions :=
  SouRdaGenAct ->
  Time -> SouRdaGenLoc -> pvaluation -> SouRdaGenLoc -> pvaluation -> Prop.

Let invariants := SouRdaGenLoc -> Time -> pvaluation -> Prop.

Let t : string := T :: voidstring.

Let d : string := D :: voidstring.

Fixpoint que_loss_has_data_to_repair (q : WAITING_RDATA_QUEUE) :
 Time -> Prop :=
  match q with
  | empty => fun s : Time => False
  | push waiting_rdata q' =>
      fun s : Time =>
      s <=/ time waiting_rdata \/ que_loss_has_data_to_repair q' s
  end.

Let guard_L1 (s : Time) (pv : pvaluation) : Prop :=
  predicate_typedvalue1_type2 que_loss_has_data_to_repair
    (pvalue pv que_loss) s.

Let inv : invariants :=
  fun (l : SouRdaGenLoc) (s : Time) (pv : pvaluation) =>
  is_type pv t Time /\
  is_type pv d nat /\
  is_type pv que_msg MESSAGE_QUEUE /\
  is_type pv que_loss WAITING_RDATA_QUEUE /\
  is_type pv txw_trail nat /\
  match l with
  | SouRdaGenLoc1 => case_inv t guard_L1 l s pv
  | SouRdaGenLoc2 => urgent_inv t l s pv
  end.

Fixpoint first_outstanding_waiting_rdata (q : WAITING_RDATA_QUEUE) :
 Time -> WAITING_RDATA -> Prop :=
  match q with
  | empty => fun (s : Time) (wr : WAITING_RDATA) => False
  | push waiting_rdata q' =>
      fun (s : Time) (wr : WAITING_RDATA) =>
      s <=/ time waiting_rdata /\ wr = waiting_rdata \/
      time waiting_rdata </ s \/ first_outstanding_waiting_rdata q' s wr
  end.

Fixpoint del_waiting_rdata_from_que (q1 q2 : WAITING_RDATA_QUEUE) {struct q2} 
   : WAITING_RDATA -> Prop :=
  match q1, q2 with
  | empty, empty => fun wr : WAITING_RDATA => True
  | empty, push waiting_rdata2 q2' => fun wr : WAITING_RDATA => False
  | push waiting_rdata1 q1', empty =>
      fun wr : WAITING_RDATA =>
      waiting_rdata1 = wr /\ q1' = empty WAITING_RDATA
  | push waiting_rdata1 q1', push waiting_rdata2 q2' =>
      fun wr : WAITING_RDATA =>
      waiting_rdata1 = wr /\ q1' = q2 \/
      waiting_rdata1 <> wr /\
      waiting_rdata1 = waiting_rdata2 /\
      del_waiting_rdata_from_que q1' q2' wr
  end.

Let L1_L2 (a : SouRdaGenAct) (s : Time) (pv1 pv2 : pvaluation) : Prop :=
  a = SouRdaGenActWrite que_loss /\
  case_trans_out guard_L1 a s SouRdaGenLoc1 pv1 SouRdaGenLoc2 pv2 /\
  urgent_trans_in t a s SouRdaGenLoc1 pv1 SouRdaGenLoc2 pv2 /\
  (forall wr : WAITING_RDATA,
   predicate_typedvalue1_type2
     (fun (q : WAITING_RDATA_QUEUE) (wr : WAITING_RDATA) =>
      first_outstanding_waiting_rdata q s wr) (pvalue pv1 que_loss) wr ->
   predicate_typedvalue1_typedvalue2
     (fun q1 q2 : WAITING_RDATA_QUEUE => del_waiting_rdata_from_que q1 q2 wr)
     (pvalue pv1 que_loss) (pvalue pv2 que_loss) /\
   pvalue pv2 d = Build_typedvalue (time wr)) /\
  eq_pvaluation (prestrict (prestrict (prestrict pv1 t) que_loss) d)
    (prestrict (prestrict (prestrict pv2 t) que_loss) d).

Let push_waiting_rdata (trail sqn : nat) (q1 q2 : MESSAGE_QUEUE) :=
  q2 = push (RDATA trail sqn) q1.

Let L2_L1 (a : SouRdaGenAct) (s : Time) (pv2 pv1 : pvaluation) : Prop :=
  a = SouRdaGenActWrite que_msg /\
  urgent_trans_out t a s SouRdaGenLoc1 pv1 SouRdaGenLoc2 pv2 /\
  case_trans_in t a s SouRdaGenLoc1 pv1 SouRdaGenLoc2 pv2 /\
  (forall trail sqn : nat,
   pvalue pv2 txw_trail = Build_typedvalue trail /\
   pvalue pv2 d = Build_typedvalue sqn ->
   predicate_typedvalue1_typedvalue2
     (fun q1 q2 : MESSAGE_QUEUE => push_waiting_rdata trail sqn q1 q2)
     (pvalue pv2 que_msg) (pvalue pv1 que_msg)) /\
  eq_pvaluation (prestrict (prestrict pv2 t) que_msg)
    (prestrict (prestrict pv1 t) que_msg).

Let trans : transitions :=
  fun (a : SouRdaGenAct) (s : Time) (l1 : SouRdaGenLoc) 
    (pv1 : pvaluation) (l2 : SouRdaGenLoc) (pv2 : pvaluation) =>
  match l1, l2 with
  | SouRdaGenLoc1, SouRdaGenLoc2 => L1_L2 a s pv1 pv2
  | SouRdaGenLoc2, SouRdaGenLoc1 => L2_L1 a s pv1 pv2
  | _, _ => False
  end.

Let is_critical (str : string) (l : SouRdaGenLoc) : Prop :=
  str = que_loss /\ l = SouRdaGenLoc2.

Definition SouRdaGen : vp_auto :=
  Build_vp_auto sharedvariables (Auto:=Build_p_auto inv trans) is_critical.

End SOURCE_RDATA_GENERATION_DEF.


(*****************************************************)
(*                                                   *)
(*  Transmission Procedure                           *)
(*                                                   *)
(*****************************************************)

Variable MAX_TIME_PER_MESSAGE : Time.

Section SOURCE_TRANSMISSION_PROCEDURE_DEF.

Let sharedvariables : list string := que_msg :: nil.

Inductive SouTransProcLoc : Set :=
  | SouTransProcLoc1 : SouTransProcLoc
  | SouTransProcLoc2 : SouTransProcLoc
  | SouTransProcLoc3 : SouTransProcLoc
  | SouTransProcLoc4 : SouTransProcLoc
  | SouTransProcLoc5 : SouTransProcLoc.

Inductive SouTransProcAct : Set :=
  | SouTransProcActTau : SouTransProcAct
  | SouTransProcActChOut : SouTransProcAct
  | SouTransProcActWrite : string -> SouTransProcAct.

Let transitions :=
  SouTransProcAct ->
  Time ->
  SouTransProcLoc -> pvaluation -> SouTransProcLoc -> pvaluation -> Prop.

Let invariants := SouTransProcLoc -> Time -> pvaluation -> Prop.

Let SouTransProc_ch_out := Build_channel ch_out SouTransProcActChOut.

Let t : string := T :: voidstring.
Let t1 : string := T :: t.

Let d : string := D :: voidstring.

Let guard_L2 (s : Time) (pv : pvaluation) : Prop :=
  ge_time_typedvalue s (pvalue pv t1) /\
  predicate_typedvalue (fun q : MESSAGE_QUEUE => queue_length q > 0)
    (pvalue pv que_loss).

Let inv : invariants :=
  fun (l : SouTransProcLoc) (s : Time) (pv : pvaluation) =>
  is_type pv t Time /\
  is_type pv t1 Time /\
  is_type pv d MESSAGE /\
  is_type pv que_msg MESSAGE_QUEUE /\
  match l with
  | SouTransProcLoc1 => urgent_inv t l s pv
  | SouTransProcLoc2 => case_inv t guard_L2 l s pv
  | SouTransProcLoc3 => send_inv_l1 t SouTransProc_ch_out l s pv
  | SouTransProcLoc4 => send_inv_l2 t l s pv
  | SouTransProcLoc5 => send_inv_l3 t l s pv
  end.

Let L1_L2 (a : SouTransProcAct) (s : Time) (pv1 pv2 : pvaluation) : Prop :=
  a = SouTransProcActTau /\
  urgent_trans_out t a s SouTransProcLoc1 pv1 SouTransProcLoc2 pv2 /\
  case_trans_in t a s SouTransProcLoc1 pv1 SouTransProcLoc2 pv2 /\
  eq_time_typedvalue s (pvalue pv2 t1) /\
  eq_pvaluation (prestrict (prestrict pv1 t) t1)
    (prestrict (prestrict pv2 t) t1).

Let pop_waiting_message (q : MESSAGE_QUEUE) (msg : MESSAGE) :=
  msg = pop_ele_que_msg q.
Let del_waiting_message (q1 q2 : MESSAGE_QUEUE) := q2 = pop_que_que_msg q1.

Let L2_L3 (a : SouTransProcAct) (s : Time) (pv2 pv3 : pvaluation) : Prop :=
  a = SouTransProcActWrite que_msg /\
  case_trans_out guard_L2 a s SouTransProcLoc2 pv2 SouTransProcLoc3 pv3 /\
  send_trans_l1_in t a s SouTransProcLoc2 pv2 SouTransProcLoc3 pv3 /\
  predicate_typedvalue1_typedvalue2 pop_waiting_message 
    (pvalue pv2 que_msg) (pvalue pv3 d) /\
  predicate_typedvalue1_typedvalue2 del_waiting_message 
    (pvalue pv2 que_msg) (pvalue pv3 que_msg) /\
  eq_time_typedvalue (s +/ MAX_TIME_PER_MESSAGE) (pvalue pv3 t1) /\
  eq_pvaluation
    (prestrict (prestrict (prestrict (prestrict pv2 t) t1) d) que_msg)
    (prestrict (prestrict (prestrict (prestrict pv3 t) t1) d) que_msg).

Let L3_L4 (a : SouTransProcAct) (s : Time) (pv3 pv4 : pvaluation) : Prop :=
  send_trans_l1_l2 t SouTransProcActWrite SouTransProc_ch_out 
    (pvalue pv3 d) a s SouTransProcLoc3 pv3 SouTransProcLoc4 pv4.

Let L4_L5 (a : SouTransProcAct) (s : Time) (pv4 pv5 : pvaluation) : Prop :=
  send_trans_l2_l3 t SouTransProc_ch_out MESSAGE_PASSING_TIME a s
    SouTransProcLoc4 pv4 SouTransProcLoc5 pv5.

Let L5_L2 (a : SouTransProcAct) (s : Time) (pv5 pv2 : pvaluation) : Prop :=
  a = SouTransProcActTau /\
  send_trans_l3_out t a s SouTransProcLoc5 pv5 SouTransProcLoc2 pv2 /\
  case_trans_in t a s SouTransProcLoc5 pv5 SouTransProcLoc2 pv2 /\
  eq_pvaluation (prestrict pv5 t) (prestrict pv2 t).

Let trans : transitions :=
  fun (a : SouTransProcAct) (s : Time) (l1 : SouTransProcLoc)
    (pv1 : pvaluation) (l2 : SouTransProcLoc) (pv2 : pvaluation) =>
  match l1, l2 with
  | SouTransProcLoc1, SouTransProcLoc2 => L1_L2 a s pv1 pv2
  | SouTransProcLoc2, SouTransProcLoc3 => L2_L3 a s pv1 pv2
  | SouTransProcLoc3, SouTransProcLoc4 => L3_L4 a s pv1 pv2
  | SouTransProcLoc4, SouTransProcLoc5 => L4_L5 a s pv1 pv2
  | SouTransProcLoc5, SouTransProcLoc2 => L5_L2 a s pv1 pv2
  | _, _ => False
  end.

Let is_critical (str : string) (l : SouTransProcLoc) : Prop :=
  send_is_critical_l2 SouTransProc_ch_out str SouTransProcLoc4 l.

Definition SouTransProc : vp_auto :=
  Build_vp_auto sharedvariables (Auto:=Build_p_auto inv trans) is_critical.

End SOURCE_TRANSMISSION_PROCEDURE_DEF.


(*****************************************************)
(*                                                   *)
(*  TXW Advance                                      *)
(*                                                   *)
(*****************************************************)

Variable TXW_INC : nat.
Variable TXW_ADV_IVL : Time.
Variable TXW_BYTES : nat.

Section SOURCE_TXW_ADVANCE_DEF.

Let sharedvariables : list string :=
  txw_lead :: txw_trail :: que_loss :: que_msg :: nil.

Inductive SouTxwAdvLoc : Set :=
  | SouTxwAdvLoc1 : SouTxwAdvLoc
  | SouTxwAdvLoc2 : SouTxwAdvLoc
  | SouTxwAdvLoc3 : SouTxwAdvLoc
  | SouTxwAdvLoc4 : SouTxwAdvLoc
  | SouTxwAdvLoc5 : SouTxwAdvLoc.

Inductive SouTxwAdvAct : Set :=
  | SouTxwAdvActTau : SouTxwAdvAct
  | SouTxwAdvActWrite : string -> SouTxwAdvAct.

Let transitions :=
  SouTxwAdvAct ->
  Time -> SouTxwAdvLoc -> pvaluation -> SouTxwAdvLoc -> pvaluation -> Prop.

Let invariants := SouTxwAdvLoc -> Time -> pvaluation -> Prop.

Let t : string := T :: voidstring.
Let t1 : string := T :: t.

(*  Here we implement the "Advance with Data"        *)
(*  strategy                                         *)

Let txw_is_full (trail lead : nat) : Prop := trail - lead >= TXW_BYTES.

Let guard_L1 (s : Time) (pv : pvaluation) : Prop :=
  predicate_typedvalue1_typedvalue2 txw_is_full (pvalue pv txw_trail)
    (pvalue pv txw_lead).

Fixpoint no_rdata_in_txw_inc (q : MESSAGE_QUEUE) : 
 nat -> Prop :=
  match q with
  | empty => fun trail : nat => True
  | push msg q' =>
      fun trail : nat =>
      match msg with
      | ODATA tr sqn => sqn > trail + TXW_INC /\ no_rdata_in_txw_inc q' trail
      | RDATA tr sqn => sqn > trail + TXW_INC /\ no_rdata_in_txw_inc q' trail
      | _ => no_rdata_in_txw_inc q' trail
      end
  end.

Let guard_L2 (s : Time) (pv : pvaluation) : Prop :=
  predicate_typedvalue1_typedvalue2 no_rdata_in_txw_inc 
    (pvalue pv que_msg) (pvalue pv txw_trail).

Fixpoint rdata_in_txw_inc (q : MESSAGE_QUEUE) : nat -> Prop :=
  match q with
  | empty => fun trail : nat => False
  | push msg q' =>
      fun trail : nat =>
      match msg with
      | ODATA tr sqn =>
          sqn <= trail + TXW_INC \/ no_rdata_in_txw_inc q' trail
      | RDATA tr sqn => sqn > trail + TXW_INC \/ no_rdata_in_txw_inc q' trail
      | _ => rdata_in_txw_inc q' trail
      end
  end.

Let guard_L3_1 (s : Time) (pv : pvaluation) : Prop :=
  predicate_typedvalue1_typedvalue2 rdata_in_txw_inc 
    (pvalue pv que_msg) (pvalue pv txw_trail).

Let guard_L3_2 (s : Time) (pv : pvaluation) : Prop :=
  eq_time_typedvalue s (pvalue pv t1).

Let guard_L3 (s : Time) (pv : pvaluation) : Prop :=
  guard_L3_1 s pv \/ guard_L3_2 s pv.

Let inv : invariants :=
  fun (l : SouTxwAdvLoc) (s : Time) (pv : pvaluation) =>
  is_type pv t Time /\
  is_type pv t1 Time /\
  is_type pv que_msg MESSAGE_QUEUE /\
  is_type pv que_loss WAITING_RDATA_QUEUE /\
  is_type pv txw_trail nat /\
  match l with
  | SouTxwAdvLoc1 => case_inv t guard_L1 l s pv
  | SouTxwAdvLoc2 => case_inv t guard_L2 l s pv
  | SouTxwAdvLoc3 => case_inv t guard_L3 l s pv
  | SouTxwAdvLoc4 => urgent_inv t l s pv
  | SouTxwAdvLoc5 => urgent_inv t l s pv
  end.


Let L1_L2 (a : SouTxwAdvAct) (s : Time) (pv1 pv2 : pvaluation) : Prop :=
  a = SouTxwAdvActTau /\
  case_trans_out guard_L1 a s SouTxwAdvLoc1 pv1 SouTxwAdvLoc2 pv2 /\
  case_trans_in t a s SouTxwAdvLoc1 pv1 SouTxwAdvLoc2 pv2 /\
  eq_pvaluation (prestrict pv1 t) (prestrict pv2 t).

Let L2_L3 (a : SouTxwAdvAct) (s : Time) (pv2 pv3 : pvaluation) : Prop :=
  a = SouTxwAdvActTau /\
  case_trans_out guard_L2 a s SouTxwAdvLoc2 pv2 SouTxwAdvLoc3 pv3 /\
  case_trans_in t a s SouTxwAdvLoc2 pv2 SouTxwAdvLoc3 pv3 /\
  eq_time_typedvalue (s +/ TXW_ADV_IVL) (pvalue pv3 t1) /\
  eq_pvaluation (prestrict (prestrict pv2 t) t1)
    (prestrict (prestrict pv3 t) t1).

Let L3_L2 (a : SouTxwAdvAct) (s : Time) (pv3 pv2 : pvaluation) : Prop :=
  a = SouTxwAdvActTau /\
  case_trans_out guard_L3_1 a s SouTxwAdvLoc3 pv3 SouTxwAdvLoc2 pv2 /\
  case_trans_in t a s SouTxwAdvLoc3 pv3 SouTxwAdvLoc2 pv2 /\
  eq_pvaluation (prestrict pv3 t) (prestrict pv2 t).

Let increase_txw_trail (trail1 trail2 : nat) : Prop :=
  trail2 = trail1 + TXW_INC.

Let L3_L4 (a : SouTxwAdvAct) (s : Time) (pv3 pv4 : pvaluation) : Prop :=
  a = SouTxwAdvActWrite txw_trail /\
  case_trans_out guard_L3_2 a s SouTxwAdvLoc3 pv3 SouTxwAdvLoc4 pv4 /\
  urgent_trans_in t a s SouTxwAdvLoc3 pv3 SouTxwAdvLoc4 pv4 /\
  predicate_typedvalue1_typedvalue2 increase_txw_trail 
    (pvalue pv3 txw_trail) (pvalue pv4 txw_trail) /\
  eq_pvaluation (prestrict (prestrict pv3 t) txw_trail)
    (prestrict (prestrict pv4 t) txw_trail).

Let obselete_msg (msg : MESSAGE) (trail : nat) : Prop :=
  match msg with
  | SPM tr ld => tr < trail
  | ODATA tr sqn => sqn < trail
  | RDATA tr sqn => sqn < trail
  | NAK sqn => sqn < trail
  | NCF sqn => sqn < trail
  | _ => False
  end.

Definition del_obselete_msg_from_que_msg (q1 q2 : MESSAGE_QUEUE)
  (trail : nat) : Prop :=
  del_que q1 q2 (fun msg : MESSAGE => obselete_msg msg trail).

Let L4_L5 (a : SouTxwAdvAct) (s : Time) (pv4 pv5 : pvaluation) : Prop :=
  a = SouTxwAdvActWrite que_msg /\
  urgent_trans_out t a s SouTxwAdvLoc4 pv4 SouTxwAdvLoc5 pv5 /\
  urgent_trans_in t a s SouTxwAdvLoc4 pv4 SouTxwAdvLoc5 pv5 /\
  (forall trail : nat,
   (pvalue pv4 txw_trail = Build_typedvalue trail ->
    predicate_typedvalue1_typedvalue2
      (fun q1 q2 : MESSAGE_QUEUE => del_obselete_msg_from_que_msg q1 q2 trail)
      (pvalue pv4 que_msg) (pvalue pv5 que_msg)) /\
   eq_pvaluation (prestrict (prestrict pv4 t) que_msg)
     (prestrict (prestrict pv5 t) que_msg)).


Let obselete_waiting_rdata (wr : WAITING_RDATA) (trail : nat) : Prop :=
  sqn wr < trail.

Definition del_obselete_waiting_rdata_from_que_loss
  (q1 q2 : WAITING_RDATA_QUEUE) (trail : nat) : Prop :=
  del_que q1 q2 (fun wr : WAITING_RDATA => obselete_waiting_rdata wr trail).

Let L5_L1 (a : SouTxwAdvAct) (s : Time) (pv5 pv1 : pvaluation) : Prop :=
  a = SouTxwAdvActWrite que_loss /\
  urgent_trans_out t a s SouTxwAdvLoc5 pv5 SouTxwAdvLoc1 pv1 /\
  case_trans_in t a s SouTxwAdvLoc5 pv5 SouTxwAdvLoc1 pv1 /\
  (forall trail : nat,
   (pvalue pv5 txw_trail = Build_typedvalue trail ->
    predicate_typedvalue1_typedvalue2
      (fun q1 q2 : WAITING_RDATA_QUEUE =>
       del_obselete_waiting_rdata_from_que_loss q1 q2 trail)
      (pvalue pv5 que_loss) (pvalue pv1 que_loss)) /\
   eq_pvaluation (prestrict (prestrict pv5 t) que_loss)
     (prestrict (prestrict pv1 t) que_loss)).

Let trans : transitions :=
  fun (a : SouTxwAdvAct) (s : Time) (l1 : SouTxwAdvLoc) 
    (pv1 : pvaluation) (l2 : SouTxwAdvLoc) (pv2 : pvaluation) =>
  match l1, l2 with
  | SouTxwAdvLoc1, SouTxwAdvLoc2 => L1_L2 a s pv1 pv2
  | SouTxwAdvLoc2, SouTxwAdvLoc3 => L2_L3 a s pv1 pv2
  | SouTxwAdvLoc3, SouTxwAdvLoc2 => L3_L2 a s pv1 pv2
  | SouTxwAdvLoc3, SouTxwAdvLoc4 => L3_L4 a s pv1 pv2
  | SouTxwAdvLoc4, SouTxwAdvLoc5 => L4_L5 a s pv1 pv2
  | SouTxwAdvLoc5, SouTxwAdvLoc1 => L5_L1 a s pv1 pv2
  | _, _ => False
  end.

Let is_critical (str : string) (l : SouTxwAdvLoc) : Prop :=
  str = txw_trail /\ l = SouTxwAdvLoc4 \/
  str = txw_trail /\ l = SouTxwAdvLoc5 \/ str = que_msg /\ l = SouTxwAdvLoc5.

Definition SouTxwAdv : vp_auto :=
  Build_vp_auto sharedvariables (Auto:=Build_p_auto inv trans) is_critical.

End SOURCE_TXW_ADVANCE_DEF.

End SOURCE_DEF.
