(********************************************************************
  Definition du block gCSMA_CD
*********************************************************************)
Add LoadPath "..".
Require Import preambule.
Require Import Contexte.
Require Import Sender.
Require Import Bus.
Import AutoLGen.

Inductive index : Set :=
  | Ind1 : forall i : nat, i < n -> index
  | Ind2 : index.
Inductive actsync : Set :=
  | begin : actsync
  | fin : actsync
  | CD : actsync
  | busy : actsync.

Module Block.
(** Synchronization of n senders and one bus *)

Definition I := index.

Definition AutoLs (i : I) : PautL :=
  match i with
  | Ind1 _ _ => sender
  | Ind2 => bus
  end.

Definition propre (v : VarName) : Prop := False.

Lemma propre_dec : forall v : VarName, {propre v} + {~ propre v}.
simple destruct v; simpl in |- *; auto.
Defined.

Definition Actsync := actsync.

Definition SyncAct (i : I) := option (P_ActL (AutoLs i)).
Definition SAct := opt_vect (fun i : I => P_ActL (AutoLs i)).

(** Action a on Sender automata k and b on Bus *)
Definition oneact (a : Sender.AutoL.Act) (b : AutoL.Act) 
  (k : nat) : SAct :=
  index_rec SyncAct (fun j _ => ifeq j k (Some a) None) (Some b).

(** Action a on all Sender automata and b on Bus *)
Definition allact (a : Sender.AutoL.Act) (b : AutoL.Act) : SAct :=
  index_rec SyncAct (fun j _ => Some a) (Some b).

Definition begin0k := oneact Sender.begin Bus.begin.
Definition fin0k := oneact Sender.fin Bus.fin.
Definition CD1 := allact Sender.CD Bus.CD.
Definition busy1 := allact Sender.busy Bus.busy.

Inductive vectsync : Actsync -> SAct -> Prop :=
  | sync_1 : forall k : nat, k < n -> vectsync begin (begin0k k)
  | sync_2 : forall k : nat, k < n -> vectsync fin (fin0k k)
  | sync_3 : vectsync CD CD1
  | sync_4 : vectsync busy busy1.

Definition Vectsync := vectsync.
End Block.

Module Synchro := AutoL_synchro Block.

(** The synchronised p-Automata structure *)
Module pAuto := Synchro.PautoSync.

(** The synchronised localised automata as an [AutoL_struct] *)
Module autoL_struct := Synchro.AutoLSync.

(** The underlying localized automata as an object *)
Definition block : PautL := Synchro.AutoL_sync.

Definition x (k : nat) (p : k < n) : Loc block :=
  Synchro.LocaleI (i:=Ind1 k p) x.

Definition y : Loc block := Synchro.LocaleI (i:=Ind2) y.

(* Definition propre := (Loc block) := (!Synchro.Propre Contexte.Sender_x I) *)

