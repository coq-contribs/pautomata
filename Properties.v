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

(*s           Links between p-automata and labelled transition systems *)



Require Import Time.
Require Import Transitions.
Require Import PAutomata.

(* Correspondance entre le système de transitions associé à la synchronisation
   locale de deux p-automates et la synchronisation des deux systèmes de 
   transitions associés aux p-automates *)

Section THEOREM_SYNCHRO.

(* On se donne deux p-automates et un vecteur de synchronisation *)
Variable Var1 Var2 : Type.
Variable Paut1 : p_auto Var1.
Variable Paut2 : p_auto Var2.
Variable Vectsync : Actsync Paut1 Paut2 -> Prop.

Let Pauts := Pauto_sync_loc Vectsync.

Definition L1 := P_auto_LTS Paut1.
Definition L2 := P_auto_LTS Paut2.
Let LTS_sync := P_auto_LTS Pauts.

(* Correspondance du vecteur de synchronisation sur les actions du produit 
   synchronisé de L1 et L2 *)
Definition LTS_Vectsync (a : act_synchro L1 L2) : Prop :=
  match a with
  | (Dis a1, Dis a2) => Vectsync (a1, a2)
  | (Temp dt, Temp dt') => dt = dt'
  | _ => False
  end.

Let LTS12_sync : LTS :=
  LTS_synchro_restr LTS_Vectsync
    (fun s : state_synchro L1 L2 =>
     let (s1, s2) := s in time_of s1 = time_of s2).

(* Projection d'une action de LTS12_sync en une action de LTS_sync, 
   une valeur bidon est prise pour les cas par défaut *)

Definition project_act_sync (a : LTS_Act LTS12_sync) : 
  LTS_Act LTS_sync :=
  match a with
  | (Dis a1, Dis a2) => Dis (P:=Pauts) (a1, a2)
  | (Temp dt, Temp dt') => Temp Pauts dt
  | _ => Temp Pauts T0
  end.

(* Projection d'une etat de LTS12_sync en un état de LTS_sync *)

Definition project_state_sync (s : LTS_State LTS12_sync) :
  LTS_State LTS_sync :=
  match s with
  | pairT (Build_P_state l t v) (Build_P_state l' t' v') =>
      Build_P_state (P:=Pauts) (l, l') t (pairT v v')
  end.

(* Projection d'une action de LTS_sync en une action de LTS12_sync *)

Definition project_act_sync2 (a : LTS_Act LTS_sync) : 
  LTS_Act LTS12_sync :=
  match a with
  | Temp dt => (Temp Paut1 dt, Temp Paut2 dt)
  | Dis (a1, a2) => (Dis (P:=Paut1) a1, Dis (P:=Paut2) a2)
  end.

(* Projection d'une etat de LTS_sync en un état de LTS12_sync *)

Definition project_state_sync2 (s : LTS_State LTS_sync) :
  LTS_State LTS12_sync :=
  match s with
  | Build_P_state (l, l') t (pairT v v') =>
      pairT (Build_P_state l t v) (Build_P_state l' t v')
  end.

(* La synchronisation des systemes de transitions 	*)
(* sous-jacent de 2 Pautomates est identique au   	*)
(* systeme de transitions sous-jacent a la        	*)
(* synchronisation des deux Pautomates  en se 		*)
(* restreignant aux couples d'états qui partagent le 	*)
(* même temps                                           *)

Lemma LTS12_to_LTS :
 forall (s s' : LTS_State LTS12_sync) (a : LTS_Act LTS12_sync),
 LTS_Trans s a s' ->
 LTS_Trans (project_state_sync s) (project_act_sync a)
   (project_state_sync s').

intros ((l1, t1, v1), (l2, t2, v2)) ((l'1, t'1, v'1), (l'2, t'2, v'2))
 (A1, A2); simple destruct 1.
simpl in |- *; case A1.
(* A1 = Dis a1 *)
intro a1; case A2.
	(* A2 = Dis a2 *)
intro a2; intros.
inversion_clear H3; inversion_clear H4.
simpl in H5, H6, H3, H7.
rewrite <- H6.
red in |- *.
constructor; simpl in |- *; auto.
red in |- *; simpl in |- *; repeat split; auto.
rewrite H1; auto.
	(* A2 = Temp t *)
contradiction.
(* A1 = Temp dt1 *)
intro dt1; case A2.
	(* A2 = Dis a1 *)
contradiction.
	(* A2 = Temp dt2 *)
intro dt2; unfold P_transition in |- *; intros.
inversion_clear H3; inversion_clear H4.
simpl in H6, H8.
injection H6; injection H8; intros.
constructor 2; simpl in |- *; trivial.
rewrite H4; rewrite H13; rewrite H12; rewrite H14; rewrite H11; trivial.
repeat (red in |- *; simpl in |- *).
red in H7, H9; simpl in H7, H9.
split; auto.
rewrite H1; apply H9; auto.
rewrite <- H0; trivial.
Qed.


Lemma LTS_to_LTS12 :
 forall (s s' : LTS_State LTS_sync) (A : LTS_Act LTS_sync),
 LTS_Trans s A s' ->
 LTS_Trans (project_state_sync2 s) (project_act_sync2 A)
   (project_state_sync2 s').

intros ((l1, l2), t, (v1, v2)) ((l'1, l'2), t', (v'1, v'2)) A.
simple destruct 1; unfold loc_of, val_of, time_of in |- *.
(* A = Dis (a1,a2) *)
intros (a1, a2); intros.
unfold project_state_sync2, project_act_sync2 in |- *.
case H0; simpl in |- *; intros H4 (H5, H6).
constructor; simpl in |- *; auto.
constructor; auto.

constructor; simpl in |- *; auto.

(* A = Temp dt *)
intros.
unfold project_state_sync2, project_act_sync2 in |- *.
injection H1; intros.
simpl in |- *.

constructor; simpl in |- *; auto.
constructor; simpl in |- *; trivial.
rewrite H5; rewrite H7; rewrite H4; trivial.
repeat red in H2; simpl in H2.
repeat red in |- *; simpl in |- *; intros.
case (H2 T); trivial.
constructor; simpl in |- *; auto.
rewrite H6; rewrite H5; rewrite H3; trivial.
repeat red in H2; simpl in H2.
red in |- *; simpl in |- *; intros.
case (H2 T); trivial.
Qed.

End THEOREM_SYNCHRO.













