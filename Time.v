(****************************************************************************)
(* 	                 Christine Paulin-Mohring                           *)
(*                               July 1st 2000                              *)
(****************************************************************************)
(*i $Id$ i*)

(*********************************************************)
(*s          Axiomatisation of time from reals           *)
(*********************************************************)

Require Export ZArith.

Parameter Time : Set.
Parameter T0 : Time.
Parameter T1 : Time.
Parameter Tplus : Time -> Time -> Time.
Parameter Tmult : Time -> Time -> Time.
Parameter Topp : Time -> Time.
Parameter Tlt : Time -> Time -> Prop.    


(**********)
Definition Tle (r1 r2 : Time) : Prop := Tlt r1 r2 \/ r1 = r2.
Definition Tge (r1 r2 : Time) : Prop := Tle r2 r1.
Definition Tgt (r1 r2 : Time) : Prop := Tlt r2 r1.

Hint Unfold Tle Tge Tgt: time.

(**********)
Definition Tminus (r1 r2 : Time) : Time := Tplus r1 (Topp r2).

(*********************************************************)
(*s      Field axioms                                   *)
(*********************************************************)
(*********************************************************)
(*       Addition                                        *)
(*********************************************************)

(**********)
Axiom Tplus_sym : forall r1 r2 : Time, Tplus r1 r2 = Tplus r2 r1.

(**********)
Axiom
  Tplus_assoc :
    forall r1 r2 r3 : Time, Tplus (Tplus r1 r2) r3 = Tplus r1 (Tplus r2 r3).

(**********)
Axiom Tplus_Topp_r : forall r : Time, Tplus r (Topp r) = T0.

Hint Resolve Tplus_sym Tplus_Topp_r: time.

(**********)
Axiom Tplus_T0_r : forall r : Time, Tplus r T0 = r.

Lemma Tplus_T0_l : forall r : Time, Tplus T0 r = r.
intro; rewrite Tplus_sym; apply Tplus_T0_r.
Qed.

Hint Resolve Tplus_T0_r Tplus_T0_l: time.

(**********)

(*********************************************************)
(*s      Order axioms                                    *)
(*********************************************************)
(*********************************************************)
(*       Total Order                                     *)
(*********************************************************)

(**********)
Axiom
  total_order : forall r1 r2 : Time, {Tlt r1 r2} + {r1 = r2} + {Tlt r2 r1}.

(*********************************************************)
(*s      Lower than                                      *)
(*********************************************************)

(**********)
Axiom Tlt_antisym : forall r1 r2 : Time, Tlt r1 r2 -> ~ Tlt r2 r1.

(**********)
Axiom Tlt_trans : forall r1 r2 r3 : Time, Tlt r1 r2 -> Tlt r2 r3 -> Tlt r1 r3.

(**********)
Axiom
  Tlt_compatibility_l :
    forall r r1 r2 : Time, Tlt r1 r2 -> Tlt (Tplus r r1) (Tplus r r2).

Axiom Tlt_T0_T1 : Tlt T0 T1.

Hint Resolve Tlt_T0_T1 Tlt_trans Tlt_compatibility_l Tlt_antisym: time.
(**********)

(**********************************************************) 
(*s      Injection from N to Time                         *)
(**********************************************************)

(**********)
Fixpoint INTime (n : nat) : Time :=
  match n with
  | O => T0
  | S O => T1
  | S n => Tplus (INTime n) T1
  end.  

(**********************************************************) 
(*s      Injection from Z to R                            *)
(**********************************************************)

(**********)
Definition IZTime (z : Z) : Time :=
  match z with
  | Z0 => T0
  | Zpos n => INTime (nat_of_P n)
  | Zneg n => Topp (INTime (nat_of_P n))
  end.  


(*********************************************************)
(*       Multiplication                                  *)
(*********************************************************)

(**********)
Axiom Tmult_sym : forall r1 r2 : Time, Tmult r1 r2 = Tmult r2 r1.

(**********)
Axiom
  Tmult_assoc :
    forall r1 r2 r3 : Time, Tmult (Tmult r1 r2) r3 = Tmult r1 (Tmult r2 r3).

Hint Resolve Tmult_sym Tmult_assoc: time.

(**********)
Axiom Tmult_T0_r : forall r : Time, Tmult r T0 = T0.

Lemma Tmult_T0_l : forall r : Time, Tmult T0 r = T0.
intro; rewrite Tmult_sym; apply Tmult_T0_r.
Qed.

(**********)
Axiom Tmult_T1_r : forall r : Time, Tmult r T1 = r.

Lemma Tmult_T1_l : forall r : Time, Tmult T1 r = r.
intro; rewrite Tmult_sym; apply Tmult_T1_r.
Qed.


Hint Resolve Tmult_T0_r Tmult_T0_l: time.