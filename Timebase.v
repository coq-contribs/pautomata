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
(*                               Timebase.v                                 *)
(* 	                 Christine Paulin-Mohring                           *)
(*                               July 1st 2000                              *)
(****************************************************************************)

(**************************************************************************)
(*  Basic lemmas for Time, based on similar results for reals numbers     *)
(**************************************************************************)

Require Export Time.
Require Import TimeSyntax.
Require Import ZArithRing.
Require Import Omega.

Unset Standard Proposition Elimination Names.

(**************************************************************************)
(*                            Basic Lemmas                                *)
(**************************************************************************)
Lemma Tle_refl : forall r : Time, r <=/ r.
auto with time.
Qed.

Lemma Tlt_le : forall r1 r2 : Time, r1 </ r2 -> r1 <=/ r2.
auto with time.
Qed.

Hint Resolve Tle_refl Tlt_le: time.

Lemma Tlt_antirefl : forall r : Time, ~ r </ r.
red in |- *; intros r H.
apply (Tlt_antisym r r H H); trivial.
Qed.

Hint Resolve Tlt_antirefl: time.

Lemma Tlt_not_eq : forall r1 r2 : Time, r1 </ r2 -> r1 <> r2.
red in |- *; intros r1 r2 H H1; rewrite H1 in H.
apply (Tlt_antirefl r2); trivial.
Qed.

Hint Immediate Tlt_not_eq: time.


Lemma Tlt_not_eq_sym : forall r1 r2 : Time, r1 </ r2 -> r2 <> r1.
intros; apply sym_not_eq; auto with time.
Qed.

Hint Immediate Tlt_not_eq_sym: time.

Lemma Tlt_not_le : forall r1 r2 : Time, r1 </ r2 -> ~ r2 <=/ r1.
red in |- *; intros r1 r2 H H1.
case H1.
intro H2; exact (Tlt_antisym r1 r2 H H2).
intro H2; rewrite H2 in H; apply (Tlt_antirefl r1); trivial.
Qed.

Lemma Tle_not_lt : forall r1 r2 : Time, r1 <=/ r2 -> ~ r2 </ r1.
red in |- *; intros r1 r2 H H1.
case H.
intro H2; exact (Tlt_antisym r2 r1 H1 H2).
intro H2; rewrite H2 in H1; apply (Tlt_antirefl r2); trivial.
Qed.

Hint Resolve Tlt_not_le Tle_not_lt: time.


(**********)
Lemma Teq_dec : forall r1 r2 : Time, {r1 = r2} + {r1 <> r2}.
intros r1 r2; case (total_order r1 r2).
simple destruct 1; auto with time.
auto with time.
Qed.

(**********)
Lemma total_order_Tle : forall r1 r2 : Time, {r1 <=/ r2} + {~ r1 <=/ r2}.
intros r1 r2; case (total_order r1 r2).
simple destruct 1; auto with time.
auto with time.
Qed.

(**********)
Lemma Tlt_dec : forall r1 r2 : Time, r1 <> r2 -> {r1 </ r2} + {r2 </ r1}.
intros; case (total_order r1 r2); intros.
case s; auto.
intro H1; absurd (r1 = r2); trivial.
auto.
Qed.

(**********)
Lemma Tle_lt_dec : forall r1 r2 : Time, {r1 <=/ r2} + {r2 </ r1}.
intros r1 r2; case (total_order r1 r2).
simple destruct 1; auto with time.
auto with time.
Qed.


(*********************************************************)
(*         Field Lemmas                                  *)
(*********************************************************)
(*********************************************************)
(*       Addition                                        *)
(*********************************************************)

(**********)
Lemma Tplus_Topp_l : forall r : Time, Topp r +/ r = T0.
  intro; rewrite Tplus_sym; auto with time.
Qed.

Hint Resolve Tplus_Topp_l: time.
(**********)

Lemma Tplus_Tplus_Topp_l_l : forall r1 r2 : Time, Topp r1 +/ r1 +/ r2 = r2.
  intros; rewrite Tplus_Topp_l; auto with time.
Qed.

Hint Resolve Tplus_Tplus_Topp_l_l: time.

Lemma Tplus_Tplus_Topp_l_r : forall r1 r2 : Time, r1 +/ (Topp r2 +/ r2) = r1.
  intros; rewrite Tplus_Topp_l; auto with time.
Qed.

Hint Resolve Tplus_Tplus_Topp_l_r: time.

Lemma Tplus_Tplus_Topp_r_l : forall r1 r2 : Time, r1 +/ Topp r1 +/ r2 = r2.
  intros; rewrite Tplus_Topp_r; auto with time.
Qed.

Hint Resolve Tplus_Tplus_Topp_r_l: time.

Lemma Tplus_Tplus_Topp_r_r : forall r1 r2 : Time, r1 +/ (r2 +/ Topp r2) = r1.
  intros; rewrite Tplus_Topp_r; auto with time.
Qed.

Hint Resolve Tplus_Tplus_Topp_r_r: time.



(**********)
Lemma Tplus_Topp : forall x y : Time, x +/ y = T0 -> Topp x = y.
  intros; rewrite <- (Tplus_Tplus_Topp_l_l x y).
  rewrite Tplus_assoc; rewrite H; auto with time.
Qed.

Hint Resolve (f_equal (A:=Time)): time.

Lemma Tplus_compat_l : forall r r1 r2 : Time, r1 = r2 -> r +/ r1 = r +/ r2.
  auto with time.
Qed.

Hint Resolve Tplus_compat_l: Time.

Lemma Tplus_compat_r : forall r r1 r2 : Time, r1 = r2 -> r1 +/ r = r2 +/ r.
  intros; rewrite (Tplus_sym r1 r); rewrite (Tplus_sym r2 r); auto with time.
Qed.

Hint Resolve Tplus_compat_r: Time.

(**********)
Lemma Tplus_simpl_l : forall r r1 r2 : Time, r +/ r1 = r +/ r2 -> r1 = r2.
  intros; rewrite <- (Tplus_Tplus_Topp_l_l r r1);
   rewrite <- (Tplus_Tplus_Topp_l_l r r2).
  repeat rewrite Tplus_assoc; rewrite <- H; reflexivity.
Qed.

Hint Immediate Tplus_simpl_l: time.

Lemma Tplus_simpl_r : forall r r1 r2 : Time, r1 +/ r = r2 +/ r -> r1 = r2.
  intros r r1 r2; rewrite (Tplus_sym r1 r); rewrite (Tplus_sym r2 r);
   eauto with time.
Qed.

Hint Resolve Tplus_simpl_r: time.


(**********)
Lemma Tplus_inv : forall r1 r2 : Time, r1 +/ r2 = r1 -> r2 = T0.
  intros r1 r2; pattern r1 at 2 in |- *; replace r1 with (r1 +/ T0);
   eauto with time.
Qed.

(*********************************************************)
(*       Opposite                                        *)
(*********************************************************)

(**********)
Lemma Topp_Topp : forall r : Time, Topp (Topp r) = r.
  intro; apply Tplus_Topp; auto with time.
Qed.

(**********)
Lemma Topp_O : Topp T0 = T0.
  apply Tplus_Topp; auto with time.
Qed.

Hint Resolve Topp_Topp Topp_O: time.

(**********)
Lemma Topp_Tplus_distr :
 forall r1 r2 : Time, Topp (r1 +/ r2) = Topp r1 +/ Topp r2.
  intros; apply Tplus_Topp.
  rewrite (Tplus_sym (Topp r1) (Topp r2)).
  repeat rewrite <- Tplus_assoc.
  rewrite (Tplus_assoc r1 r2).
  rewrite Tplus_Tplus_Topp_r_r; auto with time.
Qed.

Hint Resolve Topp_Tplus_distr: time.

(**********)
Lemma Topp_Tminus_distr : forall r1 r2 : Time, Topp (r1 -/ r2) = r2 -/ r1.
unfold Tminus in |- *; intros.
rewrite Topp_Tplus_distr.
rewrite Topp_Topp; auto with time.
Qed.

(**********)
Lemma eq_Tminus : forall r1 r2 : Time, r1 = r2 -> r1 -/ r2 = T0.
  intros; rewrite H; unfold Tminus in |- *; auto with time.
Qed.

(**********)
Lemma Tminus_eq : forall r1 r2 : Time, r1 -/ r2 = T0 -> r1 = r2.
  intros r1 r2; unfold Tminus in |- *; replace T0 with (r2 +/ Topp r2);
   eauto with time.
Qed.

(**********)
Lemma Tminus_eq_contra : forall r1 r2 : Time, r1 <> r2 -> r1 -/ r2 <> T0.
red in |- *; intros.
apply H; apply Tminus_eq; trivial.
Qed.

Lemma Tminus_Tplus_simpl_l :
 forall r r1 r2 : Time, r +/ r1 -/ (r +/ r2) = r1 -/ r2.
intros; rewrite (Tplus_sym r r1).
unfold Tminus in |- *.
rewrite Topp_Tplus_distr.
rewrite Tplus_assoc.
apply Tplus_compat_l.
rewrite <- Tplus_assoc; auto with time.
Qed.

Lemma Tminus_Tplus_simpl_r :
 forall r r1 r2 : Time, r1 +/ r -/ (r2 +/ r) = r1 -/ r2.
intros; rewrite (Tplus_sym r1 r); rewrite (Tplus_sym r2 r).
apply Tminus_Tplus_simpl_l.
Qed.

(**********)
Lemma eq_Topp : forall r1 r2 : Time, r1 = r2 -> Topp r1 = Topp r2.
  auto with time.
Qed.

Hint Resolve eq_Topp: time.

Lemma Topp_eq : forall r1 r2 : Time, Topp r1 = Topp r2 -> r1 = r2.
intros; rewrite <- (Topp_Topp r1); rewrite <- (Topp_Topp r2); auto with time.
Qed.

Hint Immediate Topp_eq: time.


(**********)
Lemma eq_Topp_T0 : forall r : Time, r = T0 -> Topp r = T0.
  intros; rewrite H; auto with time.
Qed.

Hint Resolve eq_Topp_T0: time.

Lemma Topp_T0 : Topp T0 = T0.
auto with time.
Qed.

Hint Resolve Topp_T0: time.

Lemma Topp_T0_eq : forall r : Time, Topp r = T0 -> r = T0.
intros; rewrite <- (Topp_Topp r); rewrite <- Topp_T0.
auto with time.
Qed.

Hint Immediate Topp_T0_eq: time.

(*********)
Lemma neq_Topp_T0 : forall r : Time, r <> T0 -> Topp r <> T0.
red in |- *; intros.
apply H; auto with time.
Qed.

(**********)
Lemma Tminus_T0 : forall r : Time, r -/ T0 = r.
unfold Tminus in |- *; rewrite Topp_T0; auto with time.
Qed.

Hint Resolve Tminus_T0: time.

(*********************************************************)
(*       Order Lemma                                     *)
(*********************************************************)
(*********************************************************)
(*       Lower                                       *)
(*********************************************************)

(**********)
Lemma Tle_eq : forall r1 r2 : Time, r1 <=/ r2 -> r2 <=/ r1 -> r1 = r2.
simple destruct 1; auto.
simple destruct 2; auto.
intro; absurd (r1 </ r2); auto with time.
Qed.

(**********)
Lemma Tle_trans : forall r1 r2 r3 : Time, r1 <=/ r2 -> r2 <=/ r3 -> r1 <=/ r3.
simple destruct 1.
simple destruct 2.
eauto with time.
simple destruct 1; trivial.
simple destruct 1; trivial.
Qed.

(**********)
Lemma Tle_lt_trans :
 forall r1 r2 r3 : Time, r1 <=/ r2 -> r2 </ r3 -> r1 </ r3.
simple destruct 1; eauto with time.
simple destruct 1; trivial.
Qed.

(**********)
Lemma Tlt_le_trans :
 forall r1 r2 r3 : Time, r1 </ r2 -> r2 <=/ r3 -> r1 </ r3.
simple destruct 2; eauto with time.
simple destruct 1; trivial.
Qed.

(**********)

Lemma Tlt_compatibility_r :
 forall r r1 r2 : Time, r1 </ r2 -> r1 +/ r </ r2 +/ r.
intros; rewrite (Tplus_sym r1 r); rewrite (Tplus_sym r2 r); auto with time.
Qed.
Hint Resolve Tlt_compatibility_r: time.


Lemma Tlt_anti_compatibility_l :
 forall r r1 r2 : Time, r +/ r1 </ r +/ r2 -> r1 </ r2.
intros.
rewrite <- (Tplus_Tplus_Topp_l_l r r1);
 rewrite <- (Tplus_Tplus_Topp_l_l r r2).
repeat rewrite Tplus_assoc.
auto with time.
Qed.
Hint Immediate Tlt_anti_compatibility_l: time.

Lemma Tlt_anti_compatibility_r :
 forall r r1 r2 : Time, r1 +/ r </ r2 +/ r -> r1 </ r2.
intros r r1 r2; rewrite (Tplus_sym r1 r); rewrite (Tplus_sym r2 r);
 eauto with time.
Qed.
Hint Immediate Tlt_anti_compatibility_r: time.

Lemma Tlt_plus_minus_r :
 forall r r1 r2 : Time, r </ r1 +/ r2 -> r -/ r2 </ r1.
intros; rewrite <- (Tplus_Tplus_Topp_r_r r1 r2).
repeat rewrite <- Tplus_assoc.
unfold Tminus in |- *; auto with time.
Qed.


Lemma Tlt_plus_minus_l :
 forall r r1 r2 : Time, r1 +/ r2 </ r -> r1 </ r -/ r2.
intros; rewrite <- (Tplus_Tplus_Topp_r_r r1 r2).
repeat rewrite <- Tplus_assoc.
unfold Tminus in |- *; auto with time.
Qed.

Lemma Tlt_minus_plus_l :
 forall r r1 r2 : Time, r -/ r1 </ r2 -> r </ r2 +/ r1.
intros; apply Tlt_anti_compatibility_r with (Topp r1).
repeat rewrite Tplus_assoc.
rewrite (Tplus_Tplus_Topp_r_r r2 r1); trivial.
Qed.

Lemma Tlt_minus_plus_r :
 forall r r1 r2 : Time, r </ r1 -/ r2 -> r +/ r2 </ r1.
intros; apply Tlt_anti_compatibility_r with (Topp r2).
repeat rewrite Tplus_assoc.
rewrite (Tplus_Tplus_Topp_r_r r r2); trivial.
Qed.

Hint Immediate Tlt_plus_minus_r Tlt_plus_minus_l Tlt_minus_plus_l
  Tlt_minus_plus_r: time.

(**********)
Lemma Tle_compatibility_l :
 forall r r1 r2 : Time, r1 <=/ r2 -> r +/ r1 <=/ r +/ r2.
simple destruct 1.
auto with time.
simple destruct 1; auto with time.
Qed.
Hint Resolve Tle_compatibility_l: time.

Lemma Tle_compatibility_r :
 forall r r1 r2 : Time, r1 <=/ r2 -> r1 +/ r <=/ r2 +/ r.
intros; rewrite (Tplus_sym r1 r); rewrite (Tplus_sym r2 r); auto with time.
Qed.
Hint Resolve Tle_compatibility_r: time.


(**********)
Lemma Tle_anti_compatibility_l :
 forall r r1 r2 : Time, r +/ r1 <=/ r +/ r2 -> r1 <=/ r2.
simple destruct 1; eauto with time.
Qed.

Lemma Tle_anti_compatibility_r :
 forall r r1 r2 : Time, r1 +/ r <=/ r2 +/ r -> r1 <=/ r2.
simple destruct 1; eauto with time.
Qed.

Hint Immediate Tle_anti_compatibility_l Tle_anti_compatibility_r: time.

Lemma Tle_plus_minus_r :
 forall r r1 r2 : Time, r <=/ r1 +/ r2 -> r -/ r2 <=/ r1.
intros; rewrite <- (Tplus_Tplus_Topp_r_r r1 r2).
repeat rewrite <- Tplus_assoc.
unfold Tminus in |- *; auto with time.
Qed.


Lemma Tle_plus_minus_l :
 forall r r1 r2 : Time, r1 +/ r2 <=/ r -> r1 <=/ r -/ r2.
intros; rewrite <- (Tplus_Tplus_Topp_r_r r1 r2).
repeat rewrite <- Tplus_assoc.
unfold Tminus in |- *; auto with time.
Qed.


Lemma Tle_minus_plus_l :
 forall r r1 r2 : Time, r -/ r1 <=/ r2 -> r <=/ r2 +/ r1.
intros; apply Tle_anti_compatibility_r with (Topp r1).
repeat rewrite Tplus_assoc.
rewrite (Tplus_Tplus_Topp_r_r r2 r1); trivial.
Qed.

Lemma Tle_minus_plus_r :
 forall r r1 r2 : Time, r <=/ r1 -/ r2 -> r +/ r2 <=/ r1.
intros; apply Tle_anti_compatibility_r with (Topp r2).
repeat rewrite Tplus_assoc.
rewrite (Tplus_Tplus_Topp_r_r r r2); trivial.
Qed.

Hint Immediate Tle_plus_minus_r Tle_plus_minus_l Tle_minus_plus_l
  Tle_minus_plus_r: time.

(**********)
Lemma Tlt_Topp : forall r1 r2 : Time, r1 </ r2 -> Topp r2 </ Topp r1.
intros; apply Tlt_anti_compatibility_l with r2.
apply Tlt_anti_compatibility_r with r1.
rewrite Tplus_Tplus_Topp_r_l.
rewrite Tplus_assoc.
rewrite Tplus_Tplus_Topp_l_r; trivial.
Qed.
Hint Resolve Tlt_Topp: time.

(**********)
Lemma Tlt_minus : forall r1 r2 : Time, r1 </ r2 -> r1 -/ r2 </ T0.
intros; rewrite <- (eq_Tminus r2 r2); unfold Tminus in |- *; auto with time.
Qed.
Hint Resolve Tlt_minus: time.

(**********)
Lemma Tle_minus : forall r1 r2 : Time, r1 <=/ r2 -> r1 -/ r2 <=/ T0.
simple destruct 1.
auto with time.
simple destruct 1; rewrite (eq_Tminus r1 r1); trivial with time.
Qed.

(**********)
Lemma Tminus_lt : forall r1 r2 : Time, r1 -/ r2 </ T0 -> r1 </ r2.
intros; apply (Tlt_anti_compatibility_r (Topp r2)).
rewrite Tplus_Topp_r; trivial.
Qed.

(**********)
Lemma Tminus_le : forall r1 r2 : Time, r1 -/ r2 <=/ T0 -> r1 <=/ r2.
intros; apply (Tle_anti_compatibility_r (Topp r2)).
rewrite Tplus_Topp_r; trivial.
Qed.


(*********)
Lemma Tplus_lt_le :
 forall r1 r2 r3 r4 : Time, r1 </ r2 -> r3 <=/ r4 -> r1 +/ r3 </ r2 +/ r4.
intros; apply Tlt_le_trans with (r2 +/ r3); auto with time.
Qed.

(*********)
Lemma Tplus_le_lt :
 forall r1 r2 r3 r4 : Time, r1 <=/ r2 -> r3 </ r4 -> r1 +/ r3 </ r2 +/ r4.
intros; apply Tle_lt_trans with (r2 +/ r3); auto with time.
Qed.

Hint Immediate Tplus_lt_le Tplus_le_lt: time.

Lemma Tlt_Tplus_pos_r : forall r1 r2 : Time, T0 </ r2 -> r1 </ r1 +/ r2.
intros; pattern r1 at 1 in |- *; rewrite <- (Tplus_T0_r r1).
eauto with time.
Qed.

Lemma Tle_Tplus_pos_r : forall r1 r2 : Time, T0 <=/ r2 -> r1 <=/ r1 +/ r2.
intros; pattern r1 at 1 in |- *; rewrite <- (Tplus_T0_r r1).
eauto with time.
Qed.

Lemma Tlt_Tplus_pos_l : forall r1 r2 : Time, T0 </ r2 -> r1 </ r2 +/ r1.
intros; pattern r1 at 1 in |- *; rewrite <- (Tplus_T0_l r1).
eauto with time.
Qed.

Lemma Tle_Tplus_pos_l : forall r1 r2 : Time, T0 <=/ r2 -> r1 <=/ r2 +/ r1.
intros; pattern r1 at 1 in |- *; rewrite <- (Tplus_T0_l r1).
eauto with time.
Qed.

Hint Resolve Tlt_Tplus_pos_l Tle_Tplus_pos_l Tlt_Tplus_pos_r Tle_Tplus_pos_r.


(**********)
Lemma tech_Tplus : forall r s : Time, T0 <=/ r -> T0 </ s -> r +/ s <> T0.
intros; apply Tlt_not_eq_sym; rewrite <- (Tplus_T0_l T0).
eauto with time.
Qed.

Lemma T1_neq_T0 : T0 <> T1.
eauto with time.
Qed.

Hint Resolve T1_neq_T0.

(**********)
Lemma Tlt_ToppO : forall r : Time, r </ T0 -> T0 </ Topp r.
intros; rewrite <- Topp_O; auto with time.
Qed.

(**********)
Lemma Tlt_r_plus_T1 : forall r : Time, r </ r +/ T1.
intro; pattern r at 1 in |- *; rewrite <- (Tplus_T0_r r); auto with time.
Qed.

(**********)
Lemma Tlt_minus_pos : forall r1 r2 : Time, T0 </ r2 -> r1 -/ r2 </ r1.
intros; pattern r1 at 2 in |- *; rewrite <- (Tplus_T0_r r1).
unfold Tminus in |- *; apply Tlt_compatibility_l.
rewrite <- Topp_T0; eauto with time.
Qed.

Lemma Tplus_eq_T0 :
 forall a b : Time, T0 <=/ a -> T0 <=/ b -> a +/ b = T0 -> a = T0.
intros; apply Tle_eq; trivial.
apply Tle_trans with (a +/ b); eauto with time.
Qed.

(**********************************************************) 
(*       Injection from N to Time                         *)
(**********************************************************)

(**********)
Lemma S_INTime : forall n : nat, INTime (S n) = INTime n +/ T1.
intro; case n; simpl in |- *; auto with time.
Qed.

Lemma plus_INTime : forall n m : nat, INTime (n + m) = INTime n +/ INTime m. 
simple induction n; intros.
simpl in |- *; auto with time.
repeat rewrite S_INTime.
replace (S n0 + m) with (S (n0 + m)); trivial.
rewrite S_INTime.
rewrite H.
repeat rewrite Tplus_assoc.
auto with time.
Qed.


(**********)
Lemma minus_INTime :
 forall n m : nat, m <= n -> INTime (n - m) = INTime n -/ INTime m.
intros.
elim H using le_elim_rel; intros.
rewrite <- minus_n_O.
simpl in |- *; auto with time.
repeat rewrite S_INTime.
simpl in |- *; rewrite H1.
symmetry  in |- *; apply Tminus_Tplus_simpl_r.
Qed.

(**********)
Lemma INTime_le : forall n : nat, T0 <=/ INTime n.
simple induction n.
simpl in |- *; trivial with time.
intros; rewrite S_INTime.
apply Tle_trans with (INTime n0); auto with time.
Qed.
Hint Resolve INTime_le: time.

Lemma INTime_lt : forall n : nat, T0 </ INTime (S n).
intros; apply Tle_lt_trans with (INTime n); auto with time.
rewrite S_INTime; auto with time.
Qed.
Hint Resolve INTime_lt: time.

(**********)
Lemma not_INTime_O : forall n : nat, INTime n <> T0 -> n <> 0.
red in |- *; intros n H H1; apply H.
rewrite H1; trivial.
Qed.

Lemma Tle_pos_stable :
 forall r1 r2 : Time, T0 <=/ r1 -> r1 <=/ r2 -> T0 <=/ r2.
intros; apply Tle_trans with r1; auto.
Qed.

Hint Immediate Tle_pos_stable: time.

Lemma Tlt_pos_stable : forall r1 r2 : Time, T0 <=/ r1 -> r1 </ r2 -> T0 </ r2.
intros; apply Tle_lt_trans with r1; auto with time.
Qed.

Hint Immediate Tlt_pos_stable: time.
