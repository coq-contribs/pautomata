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



(*s Modelisation and proof of a general ABR algorithm 
	following Rabadan \& Klay 
*)

Require Import ZArith.
Require Import Time.
Require Import TimeSyntax.
Require Import Timebase.
Require Import Omega.
Require Import Evenements.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Standard Proposition Elimination Names.

(*s Introducing $\tau_2$ and $\tau_3$ as positive times 
    such that $0 < \tau_3 < \tau_2$ *)
Parameter tau2 tau3 : Time.
Axiom Tlt_tau3_tau2 : tau3 </ tau2.
Axiom tau3_pos : T0 </ tau3.

Hint Resolve Tlt_tau3_tau2 tau3_pos: abr.

(*s Properties of $\tau_2$ \& $\tau_3$ *)

Lemma tau2_pos : T0 </ tau2.
apply Tlt_trans with tau3; auto with abr.
Qed.

Hint Resolve tau2_pos: abr.

Lemma Tlt_plus_tau3_tau2 : forall t : Time, t +/ tau3 </ t +/ tau2.
auto with time abr.
Qed.

Hint Resolve Tlt_plus_tau3_tau2: abr.

Lemma Tlt_plus_tau2_immediate :
 forall t1 t2 : Time, t1 </ t2 +/ tau3 -> t1 </ t2 +/ tau2.
eauto with time abr.
Qed.

Lemma Tlt_plus_tau3_immediate :
 forall t1 t2 : Time, t1 +/ tau2 </ t2 -> t1 +/ tau3 </ t2.
eauto with time abr.
Qed.

Lemma Tlt_plus_tau3_Tle_immediate :
 forall t1 t2 : Time, t1 +/ tau3 </ t2 -> t1 <=/ t2.
eauto with time abr.
Qed.

Hint Immediate Tlt_plus_tau2_immediate Tlt_plus_tau3_immediate
  Tlt_plus_tau3_Tle_immediate: abr.

Lemma Tle_plus_tau2_immediate :
 forall t1 t2 : Time, t1 <=/ t2 +/ tau3 -> t1 <=/ t2 +/ tau2.
intros; apply Tle_trans with (t2 +/ tau3); auto with time abr.
Qed.

Lemma Tle_plus_tau3_immediate :
 forall t1 t2 : Time, t1 +/ tau2 <=/ t2 -> t1 +/ tau3 <=/ t2.
intros; apply Tle_trans with (t1 +/ tau2); auto with time abr.
Qed.

Hint Immediate Tle_plus_tau2_immediate Tle_plus_tau3_immediate: abr.

(*s\definition{[pertinent]}
  Let $l$ be a schedule, and $t$ a time, [(pertinent l t)] written 
  $l(t)$ is the subset of 
  times in $l$ which are relevant for time $t$.\\
  An event at time $v$ (implicitly in $l$) starts to be active 
  at time $v+\tau_3$, and will will stay active at least until $v+\tau_2$
  or longer if there are no event in the schedule between $v$ and 
  $t-\tau_2$. Because 
  $t<v+\tau_2 \Ra \forall (u,\_)\in l. u\leq v \vee t < u+\tau_2$
  one can take as definition of $v\in l(t)$ the following property~:
	$(v+\tau_3 \leq t) \wedge 
	\forall (u,\_)\in l. u\leq v \vee t < u+\tau_2$
*)

Definition pertinent (l : schedule) (t v : Time) :=
  v +/ tau3 <=/ t /\
  forall_sch (fun (u : Time) (_ : RM) => u <=/ v \/ t </ u +/ tau2) l.

Hint Unfold pertinent: abr.

(*s Properties of [pertinent] \\
\property{[pertinent_add_simpl]} $v \in ((t',r)::l)(t) \Ra v \in l(t)$ \\
\property{[pertinent_add_simpl_hd]}
   $v \in ((t',r)::l)(t) \Ra t'\leq v \vee t < t'+\tau_2$ \\
\property{[pertinent_add]}
    $v \in l(t) \Ra (t'\leq v \vee t < t'+\tau_2) \Ra v \in 
   ((t',r)::l)(t)$ \\
\property{[pertinent_last]}
   $t'+\tau_3 \leq t \Ra (l < t') \Ra t'\in l(t) $ 
*)

Lemma pertinent_add_simpl :
 forall (l : schedule) (t v t' : Time) (r : RM),
 pertinent (add_sch t' r l) t v -> pertinent l t v.
intros.
case H; split; trivial.
inversion H1; trivial.
Qed.

Lemma pertinent_add_simpl_hd :
 forall (l : schedule) (t v t' : Time) (r : RM),
 pertinent (add_sch t' r l) t v -> t' <=/ v \/ t </ t' +/ tau2.
intros l t v t' r (prop1, prop2).
inversion prop2; trivial.
Qed.

Lemma pertinent_add :
 forall (l : schedule) (t v t' : Time) (r : RM),
 pertinent l t v ->
 t' <=/ v \/ t </ t' +/ tau2 -> pertinent (add_sch t' r l) t v.
intros l t v t' r (prop1, prop2) H.
split; auto with eve.
Qed.
Hint Resolve pertinent_add: abr.

Lemma pertinent_last :
 forall (l : schedule) (t t' : Time),
 t' +/ tau3 <=/ t -> Tle_sch l t' -> pertinent l t t'.
split; trivial.
apply forall_incl_sch with (2 := H0); auto with time.
Qed.

(*s\definition{[ACRA]}
  Specification of the ideal computation, taking into account 
  all events.\\
  [ACRA(l,t,x)] $\equiv \forall (v,r)\in l. v\in l(t) \Ra r \leq x 
                 \wedge \exists (v,r)\in l. v\in l(t) \wedge r=x$
*)
Definition ACRA (l : schedule) (t : Time) (x : RM) :=
  forall_sch (fun (v : Time) (rv : RM) => pertinent l t v -> (rv <= x)%Z) l /\
  exists_sch (fun (u : Time) (ru : RM) => ru = x /\ pertinent l t u) l.

Hint Unfold ACRA: abr.

(*s Properties of [ACRA], 
    relating $([ACRA]~l~t)$ and  $([ACRA]~(t',x)::l~t)$. \\
    \property{[ACRA_exists_last]}
    $t'+\tau_3 \leq t \Ra (l < t') \Ra 
        \exists (u,r) \in (t',x)::l. r=x \wedge u \in ((t',x)::l)(t)$\\
    \property{[ACRA_forall_add]}
$ (t'+\tau_3\leq t \Ra r \leq x) \Ra 
  (\forall (v,rv) \in l. v\in l(t) \Ra rv \leq x)
\Ra  (\forall (v,rv) \in (t',r)::l. v\in ((t',r)::l)(t) \Ra rv \leq x)$\\
    \property{[ACRA_inf_tau3]}
    $ t < t'+\tau_3 \Ra (\TT{ACRA}~l~t~x) \Ra (\TT{ACRA}~(t',r)::l~t~x)$ \\
\property{[ACRA_sup_tau2]}
$ t'+\tau_2 \leq t \Ra (l<t') \Ra (\TT{ACRA}~(t',r)::l~t~r)$.\\
 \property{[ACRA_add_sup]}
$ t'+\tau_3 \leq t \Ra (l<t') \Ra (\TT{ACRA}~(t',r)::l~t~r)$.\\
\property{[ACRA_add_inf]}
  $t'+\tau_3 \leq t < t'+\tau_2 \Ra (l<t')
  \Ra r<x \Ra (\TT{ACRA}~l~t~x) \Ra (\TT{ACRA}~(t',r)::l~t~x)$\\
\property{[ACRA_decr]}
 $l \leq t \Ra t+\tau_3 \leq u \leq v \Ra  (\TT{ACRA}~l~u~x) \Ra 
(\TT{ACRA}~l~v~y) \Ra y \leq x$

*)
Lemma ACRA_exists_last :
 forall (l : schedule) (t t' : Time) (x : RM),
 t' +/ tau3 <=/ t ->
 Tlt_sch l t' ->
 exists_sch
   (fun (u : Time) (r : RM) => r = x /\ pertinent (add_sch t' x l) t u)
   (add_sch t' x l).

intros; apply exists_add_head_sch; split; trivial.
apply pertinent_last; trivial.
constructor; auto with time.
apply forall_incl_sch with (2 := H0); auto with time. 
Qed.

Lemma ACRA_forall_add :
 forall (l : schedule) (t t' : Time) (r x : RM),
 (t' +/ tau3 <=/ t -> (r <= x)%Z) ->
 forall_sch (fun (v : Time) (rv : RM) => pertinent l t v -> (rv <= x)%Z) l ->
 forall_sch
   (fun (v : Time) (rv : RM) => pertinent (add_sch t' r l) t v -> (rv <= x)%Z)
   (add_sch t' r l).
constructor.
intros (prop1, prop2); auto.
apply forall_incl_sch with (2 := H0); intros.
apply H1; apply pertinent_add_simpl with t' r; trivial.
Qed.


Lemma ACRA_inf_tau3 :
 forall (l : schedule) (t : Time) (x : RM),
 ACRA l t x ->
 forall (t' : Time) (r : RM), t </ t' +/ tau3 -> ACRA (add_sch t' r l) t x.
intros l t x (prop1, prop2) t' r Hle.
split.
apply ACRA_forall_add; trivial.
intro; absurd (t </ t' +/ tau3); auto with time.

apply exists_add_tail_sch.
apply exists_incl_sch with (2 := prop2).
intros t0 r0 (prop3, (prop4, prop5)); auto with eve abr time.
Qed.

Lemma ACRA_sup_tau2 :
 forall (l : schedule) (t t' : Time) (r : RM),
 t' +/ tau2 <=/ t -> Tlt_sch l t' -> ACRA (add_sch t' r l) t r.

intros l t t' r Hlt flt. 
cut (forall v : Time, pertinent (add_sch t' r l) t v -> t' <=/ v).
intro.
split.
(* forall part *)
constructor; auto with zarith.
apply forall_incl_sch with (2 := flt).
intros t0 r0 H1 H2; absurd (t0 </ t'); auto with time.
(* exists part *)
apply ACRA_exists_last; auto with abr time.
(* Proof of  [(v:Time)(pertinent (add_sch t' r l) t v)->(t' <= v)] *)
intros v (prop1, prop2).
inversion_clear prop2.
case H; intro; trivial.
absurd (t' +/ tau2 <=/ t); auto with time.
Qed.

Lemma ACRA_add_sup :
 forall (l : schedule) (t t' : Time) (r : RM),
 t' +/ tau3 <=/ t ->
 Tlt_sch l t' ->
 forall x : RM, ACRA l t x -> (x <= r)%Z -> ACRA (add_sch t' r l) t r.

intros l t t' r Hlt flt x (fall, exi) infxr. 
split.
apply ACRA_forall_add; auto with zarith.
apply forall_incl_sch with (2 := fall).
intros; apply Z.le_trans with x; auto.
apply ACRA_exists_last; auto.
Qed.

Lemma ACRA_add_inf :
 forall (l : schedule) (t t' : Time) (r : RM),
 t' +/ tau3 <=/ t ->
 t </ t' +/ tau2 ->
 Tlt_sch l t' ->
 forall x : RM, ACRA l t x -> (x >= r)%Z -> ACRA (add_sch t' r l) t x.

intros l t t' r Hlt Hle flt x (fall, exi) infyr. 

split.
apply ACRA_forall_add; auto with zarith.

apply exists_add_tail_sch.
apply exists_incl_sch with (2 := exi).
intros t0 r0 (prop1, (prop2, prop3)); auto with abr time.
Qed.

Lemma ACRA_decr :
 forall (t : Time) (l : schedule),
 Tle_sch l t ->
 forall (u v : Time) (x y : RM),
 t +/ tau3 <=/ u -> u <=/ v -> ACRA l u x -> ACRA l v y -> (y <= x)%Z.
intros t l flt u v x y Hlt Hle (fallu, exu) (fallv, exv).
elim exists_forall_exists with (1 := exv).

intros w (rw, (p1, p2), p3).
rewrite <- p1.
apply
 (p3 (fun (v : Time) (rv : RM) => pertinent l u v -> (rv <= x)%Z))
  with (1 := fallu).

case p2; intros; split.
apply Tle_trans with (t +/ tau3); trivial.
apply Tle_compatibility_r.
apply p3 with (1 := flt).
apply forall_incl_sch with (2 := H0).
intros r0 r [C1| C2]; auto.
right; apply Tle_lt_trans with v; trivial.
Qed.

(*s\definition{[ACR]}
    Finding the correct value given an apropriate schedule, 
    first as a relation [ACR_rel] then using a fixpoint [ACR]. 
*)
 
Inductive ACR_rel (acrt : RM) (t : Time) : schedule -> RM -> Prop :=
  | ACR_rel_vide : ACR_rel acrt t vide acrt
  | ACR_rel_add_le :
      forall (t' : Time) (r : RM) (l : schedule),
      t' <=/ t -> ACR_rel acrt t (add_sch t' r l) r
  | ACR_rel_add_gt :
      forall (t' : Time) (r : RM) (l : schedule),
      t </ t' ->
      forall x : RM, ACR_rel acrt t l x -> ACR_rel acrt t (add_sch t' r l) x.

Hint Constructors ACR_rel: abr.


Fixpoint ACR (acrt : RM) (t : Time) (l : schedule) {struct l} : RM :=
  match l with
  | vide => acrt
  | add_sch t' r l' =>
      if Tle_lt_dec t' t then r else ACR acrt t l'
  end.

(*s Properties of [ACR].\\
\property{[ACR_add_le]} $t'\leq t \Ra ([ACR]~acrt~t~(t',r)::l)=r$ \\ 
\property{[ACR_add_gt]} $t < t' \Ra ([ACR]~acrt~t~(t',r)::l)=([ACR]~acrt~t~l)$ 
*)

Lemma ACR_add_le :
 forall (acrt : RM) (t t' : Time) (r : RM) (l : schedule),
 t' <=/ t -> ACR acrt t (add_sch t' r l) = r.
simpl in |- *; intros.
case (Tle_lt_dec t' t); trivial.
intro; absurd (t </ t'); auto with time.
Qed.

Lemma ACR_add_gt :
 forall (acrt : RM) (t t' : Time) (r : RM) (l : schedule),
 t </ t' -> ACR acrt t (add_sch t' r l) = ACR acrt t l.
simpl in |- *; intros.
case (Tle_lt_dec t' t); trivial.
intro; absurd (t </ t'); auto with time.
Qed.

Hint Resolve ACR_add_le ACR_add_gt.

Lemma ACR_rel_ACR :
 forall (acrt : RM) (t : Time) (l : schedule),
 ACR_rel acrt t l (ACR acrt t l).
simple induction l; simpl in |- *; auto with abr.
intros; case (Tle_lt_dec t0 t); auto with abr.
Qed.

(*s\definition{[last_val]} The last value in a schedule *)

Definition last_val (actr : RM) (ech : schedule) : RM :=
  match ech with
  | vide => actr
  | add_sch _ ru _ => ru
  end.

(*s\definition{[dec_from]} :
 [(decr_from acrt t0 l)] iff after time $t_0$, the value in $l$ are decreasing *)
Inductive decr_from (acrt : RM) (t0 : Time) : schedule -> Prop :=
  | decr_from_vide : decr_from acrt t0 vide
  | decr_from_add_stop :
      forall (t : Time) (r : RM) (ech : schedule),
      t <=/ t0 -> decr_from acrt t0 (add_sch t r ech)
  | decr_from_add_rec :
      forall (t : Time) (r : RM) (ech : schedule),
      (r < last_val acrt ech)%Z ->
      decr_from acrt t0 ech -> decr_from acrt t0 (add_sch t r ech).

Hint Constructors decr_from: abr.

(*s Properties of [decr_from] *)
Lemma decr_from_ACR_sup_last :
 forall (acrt : RM) (t0 u : Time),
 t0 <=/ u ->
 forall ech : schedule,
 decr_from acrt t0 ech -> (last_val acrt ech <= ACR acrt u ech)%Z.

simple induction 2.
simpl in |- *; auto with zarith.
intros.
rewrite ACR_add_le; auto with zarith.
apply Tle_trans with t0; auto with time.
intros.
simpl in |- *; case (Tle_lt_dec t u); auto with zarith.
Qed.

Lemma decr_from_ACR_add :
 forall (acrt r : RM) (t0 t u : Time),
 t0 <=/ u ->
 forall ech : schedule,
 decr_from acrt t0 (add_sch t r ech) -> (r <= ACR acrt u (add_sch t r ech))%Z.

intros.
pattern r at 1 in |- *; replace r with (last_val acrt (add_sch t r ech));
 auto.
apply decr_from_ACR_sup_last with t0; trivial.
Qed.


Lemma decr_from_last :
 forall (acrt : RM) (t0 : Time) (ech : schedule),
 Tlt_sch ech t0 -> decr_from acrt t0 ech.
simple induction 1; auto with abr time.
Qed.

Lemma decr_from_inf :
 forall (acrt : RM) (t0 t1 : Time) (ech : schedule),
 t1 </ t0 -> decr_from acrt t1 ech -> decr_from acrt t0 ech.
simple induction 2; intros; auto with abr.
constructor; apply Tle_trans with t1; auto with time.
Qed.


Lemma decr_from_inv :
 forall (acrt : RM) (t0 t : Time) (r : RM) (ech : schedule),
 decr_from acrt t0 (add_sch t r ech) ->
 sorted_sch (add_sch t r ech) -> decr_from acrt t0 ech.
intros.
inversion_clear H; trivial.
inversion_clear H0.
apply decr_from_last.
red in |- *; apply forall_incl_sch with (2 := H).
intros; apply Tlt_le_trans with t; trivial.
Qed.
     
Lemma decr_from_ACR_decr :
 forall (acrt : RM) (t0 u v : Time),
 u <=/ v ->
 t0 <=/ u ->
 forall ech : schedule,
 decr_from acrt t0 ech -> (ACR acrt v ech <= ACR acrt u ech)%Z.
simple induction 3.
simpl in |- *; auto with zarith.
intros.
rewrite ACR_add_le.
rewrite ACR_add_le; auto with zarith.
apply Tle_trans with u; auto with time.
apply Tle_trans with t0; auto with time.
apply Tle_trans with t0; auto with time.
apply Tle_trans with u; auto with time.
intros.
case (Tle_lt_dec t u); intros.
rewrite ACR_add_le; trivial.
rewrite ACR_add_le; auto with zarith.
apply Tle_trans with u; auto with time.
rewrite ACR_add_gt with (t := u); auto with Time.
case (Tle_lt_dec t v); intros.
rewrite ACR_add_le; auto with zarith.
apply Z.le_trans with (last_val acrt ech0); auto with zarith.
apply decr_from_ACR_sup_last with (2 := H3); trivial.
rewrite ACR_add_gt; auto with zarith.
Qed.

(*s\definition{[ACR_inv]}
    [ACR_inv] is an invariant on selected schedules at time $t$, 
    they are sorted with respect to time, 
    they only contain events between $t$  and $t+\tau_2$ 
    cells are decreasing from $t+\tau_3$.
*)

Record ACR_inv (acrt : RM) (ech : schedule) (t : Time) : Prop := 
  {Acr_sorted : sorted_sch ech;
   Acr_pertinent :
    forall_sch (fun (t' : Time) (_ : RM) => t <=/ t' /\ t' <=/ t +/ tau2) ech;
   Acr_decr : decr_from acrt (t +/ tau3) ech}.

Hint Resolve Build_ACR_inv: abr.

Lemma ACR_inv_inv :
 forall (acrt : RM) (t0 t : Time) (r : RM) (ech : schedule),
 ACR_inv acrt (add_sch t r ech) t0 -> ACR_inv acrt ech t0.
simple destruct 1; split.
inversion Acr_sorted0; trivial.
inversion Acr_pertinent0; trivial.
apply decr_from_inv with (1 := Acr_decr0); trivial.
Qed.


(*s\definition{[trunc]} [trunc] removes from [ech] all [(t',r')] with [t'<=t]
    and keeps last one as [acrt] *)

Record trunc_spec (t : Time) (acrt : RM) (ech : schedule) : Set := 
  {trunc_RM : RM;
   trunc_sched : schedule;
   trunc_ACR :
    forall t' : Time,
    t <=/ t' -> ACR acrt t' ech = ACR trunc_RM t' trunc_sched;
   trunc_prefix : prefix trunc_sched ech;
   trunc_inv : ACR_inv trunc_RM trunc_sched t;
   trunc_lt : Tlt_sch trunc_sched (t +/ tau2);
   trunc_last : last_val acrt ech = last_val trunc_RM trunc_sched}.


Lemma trunc :
 forall t u : Time,
 u </ t ->
 forall (acrt : RM) (ech : schedule),
 ACR_inv acrt ech u -> trunc_spec t acrt ech.
simple induction ech; clear ech.
(* Case [ech=vide] *)
intros; exists acrt vide; auto with abr eve.
(* Case [ech=(add_sch tn rn echn)] *)
intros tn rn echn recn invn.
case (Tle_lt_dec tn t); intro.
  (* Case [tn <= t], [rn] is the new value for acrt and the rest of 
     the schedule can be ignored *)
exists rn vide; auto with abr eve.
intros; rewrite ACR_add_le; trivial.
apply Tle_trans with t; trivial.
  (* Case [tn > t], recursively compute the truncated schedule *)
case recn; clear recn.
apply ACR_inv_inv with (1 := invn).
case invn;
 intros P1 P2 P3 acrt' ech' prop1 prop2 (prop3, prop4, prop5) prop6 prop7.
exists acrt' (add_sch tn rn ech'); intros.
simpl in |- *; case (Tle_lt_dec tn t'); auto.
auto with abr eve.
repeat split; auto with abr eve.

apply prefix_sorted with (2 := P1); auto with eve.
constructor; auto with time.
split; auto with time.
inversion_clear P2.
case H0; intros; apply Tle_trans with (u +/ tau2); auto with time.
inversion_clear P3.
apply decr_from_add_stop.
apply Tle_trans with (u +/ tau3); auto with time.
constructor 3; trivial.
rewrite <- prop7; auto.
constructor; auto with abr time eve.
inversion P2; intros.
case H2; intros; apply Tle_lt_trans with (u +/ tau2); auto with time.
simpl in |- *; trivial.
Qed.


(*s\definition{[add_sup]}
  [(add_sup t r acrt ech)] produces a new schedule [ech'] such that 
   [(ACR acrt t' ech')] is the same as [(ACR acrt t' ech)] for all 
   [t' < t] and [(ACR acrt t' ech')=r]  for [t'>=t]
*)

Record add_sup_spec (u t : Time) (r acrt : RM) (ech : schedule) : Set := 
  {sup_sched : schedule;
   sup_inv : ACR_inv acrt sup_sched u;
   sup_lt :
    forall t' : Time, t' </ t -> ACR acrt t' sup_sched = ACR acrt t' ech;
   sup_ge : forall t' : Time, t <=/ t' -> ACR acrt t' sup_sched = r}.


Lemma add_sup :
 forall (t : Time) (r acrt : RM) (ech : schedule),
 ACR_inv acrt ech t -> add_sup_spec t (t +/ tau3) r acrt ech.

simple induction ech; clear ech.
(* Case [ech=vide] *)
case (Z.eq_dec acrt r); intro.
(* acrt = r *)
exists vide; auto with abr eve.
(* acrt <> r *)
exists (add_sch (t +/ tau3) r vide); auto with abr eve time.
split; auto with abr eve time.
(* Case [ech=(add_sch t0 r0 ech)] *)
intros t0 r0 ech prop inv.
set (inv_ech := ACR_inv_inv inv) in *.
case prop; clear prop; trivial.
intros ech' prop1 prop2 prop3.
case (Tle_lt_dec (t +/ tau3) t0); intro.
(* [t<=t0] removes [t0] *)
exists ech'; auto with abr; intros.
rewrite ACR_add_gt; auto.
apply Tlt_le_trans with (t +/ tau3); auto with time.
(* [t0<t], add [(t,r)] excepts when [r=r0] *)
case (Z.eq_dec r0 r); intro.
(* [r=r0] *)
exists (add_sch t0 r0 ech); auto with abr eve time; intros.
rewrite ACR_add_le; trivial.
apply Tle_trans with (t +/ tau3); auto with time.
(* [r<>r0] *)
exists (add_sch (t +/ tau3) r (add_sch t0 r0 ech)); auto with abr; intros.
case inv; intros inv1 inv2 inv3; split; auto with abr eve time.
Qed.

(*s\definition{[add_inf]}
  [(add_inf t r acrt ech)] produces a new schedule [ech'] such that 
   [(ACR acrt t' ech')] is the same as [(ACR acrt t' ech)] for all 
   [t' < t] and [(ACR acrt t' ech')=max(r,(ACR acrt t' ech))]  for [t'>=t]
*)

Record add_inf_spec (t u : Time) (r acrt : RM) (ech : schedule) : Set := 
  {inf_sched : schedule;
   inf_inv : ACR_inv acrt inf_sched t;
   inf_lt_tau3 :
    forall t' : Time,
    t' </ t +/ tau3 -> ACR acrt t' inf_sched = ACR acrt t' ech;
   inf_lt_tau2_inf :
    forall t' : Time,
    t' </ u ->
    (r <= ACR acrt t' ech)%Z -> ACR acrt t' inf_sched = ACR acrt t' ech;
   inf_lt_tau2_sup :
    forall t' : Time,
    t +/ tau3 <=/ t' ->
    t' </ u -> (r > ACR acrt t' ech)%Z -> ACR acrt t' inf_sched = r;
   inf_ge_tau2 : forall t' : Time, u <=/ t' -> ACR acrt t' inf_sched = r}.


Lemma add_inf :
 forall (t : Time) (r acrt : RM) (ech : schedule),
 ACR_inv acrt ech t ->
 (r < ACR acrt (t +/ tau3) ech)%Z ->
 forall u : Time,
 t +/ tau3 </ u ->
 u <=/ t +/ tau2 -> Tlt_sch ech u -> add_inf_spec t u r acrt ech.

simple induction ech; clear ech.
(* Case [ech=vide] *)
case (Z.eq_dec acrt r); intro.
(* acrt = r *)
exists vide; auto with abr eve.
(* acrt <> r *)
intros; exists (add_sch u r vide); auto with abr eve time.
intros; rewrite ACR_add_gt; auto with abr time.
apply Tlt_trans with (t +/ tau3); trivial.
intros; rewrite ACR_add_gt; auto with abr time.
intros; simpl in H0; absurd (r > acrt)%Z; auto with zarith.

(* Case [ech=(add_sch t0 r0 ech)] *)
intros t0 r0 ech prop inv inf u ltu1 ltu2 tlt.
case inv; intros inv1 inv2 inv3.

case (Tle_lt_dec t0 (t +/ tau3)); intro.
(* Case [t0 <= t+tau3 ] *)
rewrite ACR_add_le in inf; auto.
intros; exists (add_sch u r (add_sch t0 r0 ech)); auto with abr eve time.
intros; rewrite ACR_add_gt; auto with abr time.
apply Tlt_trans with (t +/ tau3); trivial.
intros; rewrite (ACR_add_gt acrt (t:=t') (t':=u)); auto with abr time.
rewrite ACR_add_le in H1.
absurd (r < r0)%Z; omega.
apply Tle_trans with (t +/ tau3); auto.
case (Z_le_gt_dec r r0); intro infsup.
(* Case [r <= r0] *)
case (Z_le_lt_eq_dec r r0); auto; clear infsup; intro infeq.
(* Case [r < r0] *)
intros; exists (add_sch u r (add_sch t0 r0 ech)); auto with abr eve time.
intros; rewrite ACR_add_gt; auto with time abr.
apply Tlt_trans with (t +/ tau3); trivial.
intros; absurd (r < r0)%Z; trivial.
cut (r0 <= ACR acrt t' (add_sch t0 r0 ech))%Z; auto with abr.
omega.
apply decr_from_ACR_add with (t +/ tau3); auto with zarith abr.
(* Case [r=r0] *)
intros; exists (add_sch t0 r0 ech); auto with abr eve time.
intros; absurd (r = r0); trivial.
cut (r0 <= ACR acrt t' (add_sch t0 r0 ech))%Z; auto with abr.
omega.
apply decr_from_ACR_add with (t +/ tau3); auto with zarith abr.
intros; rewrite infeq; auto with abr.
rewrite ACR_add_le; auto with abr time.
apply Tle_trans with u; auto.
inversion tlt; auto with time.
(* Case [r>r0] *)
set (inv_ech := ACR_inv_inv inv) in *.
rewrite ACR_add_gt in inf; trivial.
case prop with t0; auto with abr time; clear prop.
inversion inv2; intros.
case H1; auto.
inversion inv1; auto.
intros ech' prop1 prop2 prop3 prop4 prop5.
exists ech'; auto with abr time; intros.
rewrite ACR_add_gt; auto with abr.
apply Tlt_trans with (t +/ tau3); trivial.
case (Tle_lt_dec t0 t'); intro infeq.
rewrite ACR_add_le in H0; trivial.
absurd (r > r0)%Z; omega.
rewrite ACR_add_gt; trivial.
rewrite ACR_add_gt in H0; auto with abr.
case (Tle_lt_dec t0 t'); auto with abr time; intro infeq.
rewrite ACR_add_gt in H1; auto with abr.
apply prop5.
apply Tle_trans with u; auto.
inversion tlt; auto with time.
Qed.

(*i

(*s\definition{[add_inf]}, first as a relation then as a constructive function. 
  [(add_inf r acrt ech t1)] inserts in [ech] the value [r] if it is not already present 
  at least at [t1], 
  or earlier if there is *)

Inductive add_inf_rel [r,acrt:RM]:schedule->Time->schedule->Prop := 
   add_inf_rel_vide 
	: (t1:Time)~(acrt=r)
	->(add_inf_rel r acrt vide t1 (add_sch t1 r vide))
|  add_inf_rel_vide_eq 
	: (t1:Time)acrt=r->(add_inf_rel r acrt vide t1 vide)
|  add_inf_rel_add_rec 
	: (t1:Time)(u:Time)(ru:RM)(ech,ech':schedule)`ru<r` ->
                      (add_inf_rel r acrt ech u ech')->
                      (add_inf_rel r acrt (add_sch u ru ech) t1 ech')
|  add_inf_rel_add_stop 
	: (t1:Time)(u:Time)(ru:RM)(ech:schedule)`ru>r`-> 
          (add_inf_rel r acrt (add_sch u ru ech) t1 
			      (add_sch t1 r (add_sch u ru ech)))
|  add_inf_rel_add_eq 
	: (t1:Time)(u:Time)(ru:RM)(ech:schedule)`r=ru`-> 
          (add_inf_rel r acrt (add_sch u ru ech) t1 
		              (add_sch u ru ech)).


Hint add_inf_rel : abr := Constructors add_inf_rel.

Lemma add_inf : (r,acrt:RM)(ech:schedule)(t1:Time)
	{ech':schedule | (add_inf_rel r acrt ech t1 ech')}.
Induction ech; Clear ech.
Intro t1; Case (Z_eq_dec acrt r); Intro inf.
Exists vide; Auto with abr.
Exists (add_sch t1 r vide); Auto with abr.
Intros u ru ech add_rec t1.
Case (Z_le_gt_dec ru r); Intro inf.
Case (Z_le_lt_eq_dec ru r); Trivial; Clear inf; Intro inf.
Elim (add_rec u); Intros ech' H.
Exists ech'; Auto with abr.
Exists (add_sch u ru ech); Auto with abr.
Exists (add_sch t1 r (add_sch u ru ech)); Auto with abr.
Save.

(*s Properties of [add_inf] *)
Lemma add_inf_prop1 : 
	(r:RM)(acrt:RM)(ech:schedule)
	(t1:Time)(ech':schedule)(add_inf_rel r acrt ech t1 ech')
	->(Tlt_sch ech t1)->(sorted_sch ech)->
	  (t:Time)(t1 <=/ t)->(ACR acrt t ech')=r.
Induction 1; Clear H ech t1 ech'; Auto with abr.
Intros.
Inversion_clear H2.
Inversion_clear H3.
Apply H1; Auto with abr eve.
Apply Tle_trans with t1; Auto with time.
Intros.
Inversion_clear H0.
Rewrite ACR_add_le; Auto.
Apply Tle_trans with t1; Auto with time.
Save.

Lemma add_inf_prop2 : 
	(t0:Time)(r:RM)(acrt:RM)(ech:schedule)
	(t1:Time)(ech':schedule)(add_inf_rel r acrt ech t1 ech')
	->(t0 </ t1)->`(ACR acrt t0 ech)>=r`
	->(t:Time)(t <=/ t0)->(ACR acrt t ech')=(ACR acrt t ech).
Induction 1; Clear H ech t1 ech'; Auto with abr.
Intros.
Rewrite ACR_add_gt; Auto.
Apply Tle_lt_trans with t0; Trivial.
Intros.
Case (Tle_lt_dec u t0); Intro.
Absurd `(ACR acrt t0 (add_sch u ru ech)) >= r`; Trivial.
Rewrite ACR_add_le; Auto with zarith abr.
Rewrite ACR_add_gt; Auto with abr time.
Rewrite ACR_add_gt in H3; Auto with abr time.
Apply Tle_lt_trans with t0; Trivial.
Intros.
Rewrite ACR_add_gt with t':= t1; Auto with abr time.
Apply Tle_lt_trans with t0; Trivial.
Save.

Lemma add_inf_prop3 : 
	(r:RM)(acrt:RM)(ech:schedule)
	(t1:Time)(ech':schedule)(add_inf_rel r acrt ech t1 ech')
	->(t:Time)`(ACR acrt t ech)>=r`->(t </ t1)->
          (ACR acrt t ech')=(ACR acrt t ech).
Intros; Apply add_inf_prop2 with t0:=t t1:=t1 r:=r; Auto with time abr.
Save.

(*s [inf_after r t ech] if any value in [ech] is less than [r] 
   until we reach an element 
   of time less than [t]
   [ech = vide] is excluded because assume there is an element in [ech]
   with [value > r]
*)

Inductive inf_after [r:RM;t:Time] : schedule -> Prop := 
        inf_after_stop : (u:Time)(ru:RM)(ech:schedule)
			   (u <=/ t) -> (`ru < r`) -> (inf_after r t (add_sch u ru ech))
      | inf_after_rec : (u:Time)(ru:RM)(ech:schedule)
			   (`ru < r`) -> (inf_after r t ech) -> (inf_after r t (add_sch u ru ech)).

Lemma add_inf_prop4 : 
	(t:Time)(r:RM)(acrt:RM)(ech:schedule)
	(t1:Time)(ech':schedule)(add_inf_rel r acrt ech t1 ech')
	->(Tlt_sch ech t1)->(sorted_sch ech)->(inf_after r t ech)->(ACR acrt t ech')=r.
Induction 1; Clear H ech t1 ech'; Intros; Auto with abr.
(* Case [ech=vide] *)
Inversion_clear H2.
(* Case [ru < r], recursive call *)
Inversion_clear H3.
Inversion_clear H4.
Apply add_inf_prop1 with t1:=u ech:=ech; Auto with time.
Auto.
(* Case [ru > r] *)
Inversion_clear H1.
Case (Tle_lt_dec t1 t); Intro; Auto with abr zarith.
Rewrite ACR_add_gt; Auto with zarith time.
Inversion_clear H2.
Absurd `ru < r`; Auto with zarith.
Absurd `ru < r`; Auto with zarith.
(* Case [ru = r] *)
Inversion_clear H2.
Absurd `r=ru`; Auto with zarith.
Absurd `r=ru`; Auto with zarith.
Save.

Lemma inf_after_intro 
  : (t0:Time)(acrt,r:RM)(ech:schedule)`(ACR acrt t0 ech)>r` ->
	(decr_from acrt t0 ech)->(t:Time)(t0 </ t)->`(ACR acrt t ech)<r` 
        -> (inf_after r t ech).
Induction ech.
Simpl; Intros; Absurd `acrt < r`; Auto with zarith.
Intros.
Case (Tle_lt_dec t t1); Intro.
Apply inf_after_stop; Trivial.
Rewrite ACR_add_le in H3; Trivial.
Apply inf_after_rec; Trivial.
Rewrite ACR_add_gt in H3; Trivial.
Apply Zle_lt_trans with (ACR acrt t1 s); Trivial.
Replace r0 with (ACR acrt t (add_sch t r0 s)).
Replace (ACR acrt t1 s) with (ACR acrt t1 (add_sch t r0 s)).
Apply decr_from_ACR_decr with 3:= H1; Auto with time.
Rewrite ACR_add_gt; Trivial.
Apply ACR_add_le; Auto with time.
Rewrite ACR_add_gt in H0.
Rewrite ACR_add_gt in H3; Trivial.
Apply H; Auto with abr time.
Inversion_clear H1; Trivial.
Absurd (t0 </ t); Auto with time.
Apply Tlt_trans with t1; Trivial.
Apply Tlt_trans with t1; Trivial.
Save.

Lemma add_inf_prop5 : 
	(r:RM)(acrt:RM)(ech:schedule)
	(t1:Time)(ech':schedule)(add_inf_rel r acrt ech t1 ech')
	->(Tlt_sch ech t1)->(sorted_sch ech)->(sorted_sch ech').
Induction 1; Intros; Auto with eve.
Inversion_clear H3; Inversion_clear H4; Auto with eve.
Save.
i*)

(*s\definition{[ACRI]}
    The ideal algorithm, compute at each time a new value and 
    a new schedule which satisfies the invariant and gives
    the value for all future time which are older than the 
    oldest time of the schedule plus $\tau_3$
*)

Record ACR_res (t : Time) (l : schedule) : Set := 
  {Acrt : RM;
   Ech : schedule;
   Acra_corr :
    forall t' : Time,
    t <=/ t' -> first_time t l +/ tau3 </ t' -> ACRA l t' (ACR Acrt t' Ech);
   Acr_preserved : ACR_inv Acrt Ech t}.


Lemma ACRI : forall (t : Time) (l : schedule), events t l -> ACR_res t l.

simple induction 1; clear H l t.
(* Case [l = init] *)
intros; exists r vide; simpl in |- *; auto 10 with abr eve time zarith.
(* Case [l = (add_sch tk rk l)], acrt, ech is the schedule for l *)
intros tk t rk Tlt_t_tk l eve (acrt, ech, prop1, prop2).
(* update ech in order to remove obsoletes times *)
case (trunc Tlt_t_tk (acrt:=acrt) (ech:=ech)); trivial.
intros acrt' ech' prop1' prop2' prop3' prop4' prop5'.
case prop3'; intros inv1 inv2 inv3.
case (Z_le_gt_dec (ACR acrt' (tk +/ tau3) ech') rk); intro.
(*  [(ACR acrt' (Tplus tk tau3) ech') <= rk] *)
case (add_sup (t:=tk) rk (acrt:=acrt') (ech:=ech')); trivial.
intros ech'' prop1'' prop2'' prop3''.
exists acrt' ech''; trivial.
intros.
set (Tlt_t_t' := Tlt_le_trans _ _ _ Tlt_t_tk H) in *.
set (falltlt := forall_eve_Tlt Tlt_t_tk eve) in *.

cut (first_time t l +/ tau3 </ t').
intro ft.
case (Tle_lt_dec (tk +/ tau3) t'); intro.
(* [(tk + tau3) <= t'] *)
rewrite prop3''; trivial.
apply ACRA_add_sup with (ACR acrt' t' ech'); trivial.
rewrite <- prop1'; trivial.
apply prop1; auto with time.
apply Z.le_trans with (ACR acrt' (tk +/ tau3) ech'); trivial.
apply decr_from_ACR_decr with (3 := inv3); auto with time.
(* [t'</(tk+/tau3)] *)
rewrite prop2''; trivial.
rewrite <- (prop1' t'); trivial.
apply ACRA_inf_tau3; auto.
apply prop1; auto with time.
(* Proof of [((first_time t l)+/tau3) </ t'] *)
rewrite <- first_time_eve_add with t l tk tk rk; trivial. 
(*  [(ACR acrt' (tk +/ tau3) ech') > rk] *)
case add_inf with tk rk acrt' ech' (tk +/ tau2); auto with time abr.
omega.
intros ech'' prop1'' prop2'' prop3'' prop4'' prop5''.
exists acrt' ech''; intros; auto with abr time.
set (Tlt_t_t' := Tlt_le_trans _ _ _ Tlt_t_tk H) in *.
set (falltlt := forall_eve_Tlt Tlt_t_tk eve) in *.
cut (first_time t l +/ tau3 </ t').
intro ft.
case (Tle_lt_dec (tk +/ tau2) t'); intro.
(* [(tk + tau2) <= t'] *)
rewrite prop5''; trivial.
apply ACRA_sup_tau2; auto with abr.
(* [t' < (tk + tau2)] *)
case (Tle_lt_dec (tk +/ tau3) t'); intro.
(* [(tk + tau3) <= t'] *)
case (Z_le_gt_dec rk (ACR acrt' t' ech')); intro.
(* [rk <= (ACR acrt' t' ech')] *)
rewrite prop3''; trivial.
apply ACRA_add_inf; auto with abr time.
rewrite <- prop1'; auto with abr time.
omega.
(* [rk > (ACR acrt' t' ech')] *)
rewrite prop4''; trivial.
apply ACRA_add_sup with (ACR acrt' t' ech'); auto with abr time.
rewrite <- prop1'; auto with abr time.
omega.
(* [t'< tk+tau3] *)
rewrite prop2''; trivial.
apply ACRA_inf_tau3; auto with abr time.
rewrite <- prop1'; auto with abr time.
(* Proof of [((first_time t l)+/tau3) </ t'] *)
rewrite <- first_time_eve_add with t l tk tk rk; trivial. 

Qed.

