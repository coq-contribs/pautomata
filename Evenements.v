

(*s Proof of a general scheduling algorithm\\
    Definition of schedule as a list of pairs built from a time and a 
    cell value represented as an integer .
*)

Require Import Time.
Require Import Timebase.

Set Implicit Arguments.
Unset Strict Implicit.

Definition RM := Z.

Inductive schedule : Set :=
  | vide : schedule
  | add_sch : Time -> RM -> schedule -> schedule.

(*s\definition{[forall_sch]}
   All the objects in a schedule satisfy a property *)

Inductive forall_sch (P : Time -> RM -> Prop) : schedule -> Prop :=
  | forall_init_sch : forall_sch P vide
  | forall_add_sch :
      forall (t : Time) (r : RM) (l : schedule),
      P t r -> forall_sch P l -> forall_sch P (add_sch t r l).

Hint Constructors forall_sch: eve.

(*s\definition{[exists_sch]}
    There esists an object in a schedule which satisfies a property *)

Inductive exists_sch (P : Time -> RM -> Prop) : schedule -> Prop :=
  | exists_add_tail_sch :
      forall (t : Time) (r : RM) (l : schedule),
      exists_sch P l -> exists_sch P (add_sch t r l)
  | exists_add_head_sch :
      forall (t : Time) (r : RM) (l : schedule),
      P t r -> exists_sch P (add_sch t r l).
Hint Constructors exists_sch: eve.

(*s\definition{[Tlt_sch],[Tle_sch]}  All the elements in a schedule [l] have a time less than [t] *)
Definition Tlt_sch (l : schedule) (t : Time) :=
  forall_sch (fun (t' : Time) (_ : RM) => Tlt t' t) l.

Definition Tle_sch (l : schedule) (t : Time) :=
  forall_sch (fun (t' : Time) (_ : RM) => Tle t' t) l.

Hint Unfold Tlt_sch Tle_sch: eve.

(*s\definition{[last_sch]} the last element of a schedule, if any, satisfies a property *)

Inductive last_sch (P : Time -> RM -> Prop) : schedule -> Prop :=
  | last_init_sch : last_sch P vide
  | last_add_sch :
      forall (t : Time) (r : RM) (l : schedule),
      P t r -> last_sch P (add_sch t r l).

Hint Constructors last_sch: eve.


(*s\definition{[sorted]} A schedule is sorted by increasing time *)
Inductive sorted_sch : schedule -> Prop :=
  | sorted_init : sorted_sch vide
  | sorted_add :
      forall (t : Time) (r : RM) (l : schedule),
      Tlt_sch l t -> sorted_sch l -> sorted_sch (add_sch t r l).

Hint Constructors sorted_sch: eve.

(*s Properties of [forall_sch] and [exists_sch] *)
Section Schedule_lemma.
Variable P Q R : Time -> RM -> Prop.

Lemma forall_incl_sch :
 (forall (t : Time) (r : RM), P t r -> Q t r) ->
 forall l : schedule, forall_sch P l -> forall_sch Q l.
simple induction 2; auto with eve.
Qed.

Lemma forall_incl2_sch :
 (forall (t : Time) (r : RM), P t r -> Q t r -> R t r) ->
 forall l : schedule, forall_sch P l -> forall_sch Q l -> forall_sch R l.
simple induction 2; intros; trivial with eve.
inversion H4; constructor; auto.
Qed.

Lemma exists_incl_sch :
 (forall (t : Time) (r : RM), P t r -> Q t r) ->
 forall l : schedule, exists_sch P l -> exists_sch Q l.
simple induction 2; auto with eve.
Qed.

Lemma exists_forall_exists :
 forall l : schedule,
 exists_sch P l ->
 exists t : Time,
   (exists2 r : RM,
      P t r & (forall Q : Time -> RM -> Prop, forall_sch Q l -> Q t r)).
simple induction 1.
intros t r l0 _ (t0, (r0, Ptr, fall)).
exists t0; exists r0; trivial.
intros Q0 F; inversion F; apply (fall Q0); trivial.
intros t r l0 ptr; exists t; exists r; trivial; intros.
inversion H0; trivial.
Qed.
End Schedule_lemma.

(*s Properties of [Tlt_sch] and [Tle_sch] *)
Lemma Tlt_Tle_sch :
 forall (l : schedule) (t : Time), Tlt_sch l t -> Tle_sch l t. 
red in |- *; intros l t tlt; apply forall_incl_sch with (2 := tlt);
 auto with time.
Qed.
Hint Immediate Tlt_Tle_sch: eve.

Lemma Tlt_Tle_Tlt_sch :
 forall (l : schedule) (t t' : Time), Tlt_sch l t -> Tle t t' -> Tlt_sch l t'. 
red in |- *; intros l t t' tlt tle; apply forall_incl_sch with (2 := tlt);
 auto with time.
intros; apply Tlt_le_trans with t; auto.
Qed.
Hint Immediate Tlt_Tle_Tlt_sch: eve.

(*s Properties of [sorted_sch] *)
Lemma sorted_add_add :
 forall (t1 t2 : Time) (r1 r2 : RM) (l : schedule),
 Tlt t1 t2 ->
 sorted_sch (add_sch t1 r1 l) -> sorted_sch (add_sch t2 r2 (add_sch t1 r1 l)).
constructor; trivial.
inversion H0; constructor; auto with time eve.
apply forall_incl_sch with (2 := H3); auto with time.
intros; apply Tlt_trans with t1; trivial.
Qed.
Hint Resolve sorted_add_add: eve.

(*s\definition{[prefix]} Defining that a schedule is a prefix of another *)

Inductive prefix : schedule -> schedule -> Prop :=
  | prefix_vide : forall ech : schedule, prefix vide ech
  | prefix_add :
      forall (t : Time) (r : RM) (ech ech' : schedule),
      prefix ech ech' -> prefix (add_sch t r ech) (add_sch t r ech').

Hint Constructors prefix: eve.

(*s Properties of the [prefix] relation *)
Lemma prefix_refl : forall ech : schedule, prefix ech ech.
simple induction ech; auto with eve.
Qed.

Hint Resolve prefix_refl: eve.

Lemma prefix_forall :
 forall ech1 ech2 : schedule,
 prefix ech1 ech2 ->
 forall P : Time -> RM -> Prop, forall_sch P ech2 -> forall_sch P ech1.
simple induction 1; intros; auto with eve.
inversion H2; auto with eve.
Qed.

Lemma prefix_sorted :
 forall ech1 ech2 : schedule,
 prefix ech1 ech2 -> sorted_sch ech2 -> sorted_sch ech1.
simple induction 1; intros; auto with eve.
inversion H2.
constructor; auto.
red in |- *; apply prefix_forall with (1 := H0); trivial.
Qed.

(*s Finding the oldest time in a schedule *)
Fixpoint first_time (t : Time) (l : schedule) {struct l} : Time :=
  match l with
  | vide => t
  | add_sch u _ l => first_time u l
  end.

(*s Properties of [first_time] *)
Lemma first_time_add_default :
 forall (t : Time) (l : schedule) (t' u : Time) (ru : RM),
 first_time t (add_sch u ru l) = first_time t' (add_sch u ru l).
simpl in |- *; trivial.
Qed.

Lemma first_time_Tle :
 forall t u : Time,
 Tle t u -> forall l : schedule, Tle (first_time t l) (first_time u l).
simple destruct l; simpl in |- *; auto with time.
Qed.

Hint Resolve first_time_Tle: eve.

(*s \definition{[included_sch]} 
     inclusion between schedules *)

Definition included_sch (ech1 ech2 : schedule) :=
  forall P : Time -> RM -> Prop, forall_sch P ech2 -> forall_sch P ech1.

Lemma incl_sch_refl : forall ech : schedule, included_sch ech ech.
red in |- *; auto with eve.
Qed.

Lemma incl_sch_vide : forall ech : schedule, included_sch vide ech.
red in |- *; auto with eve.
Qed.

Lemma incl_sch_add :
 forall (t : Time) (r : RM) (ech1 ech2 : schedule),
 included_sch ech1 ech2 -> included_sch (add_sch t r ech1) (add_sch t r ech2).
red in |- *; intros.
inversion H0; auto with eve.
Qed.

Hint Resolve incl_sch_refl incl_sch_vide incl_sch_add: eve.

(*s \definition{[events]} 
     Defining that a schedule is sorted by time and ends with [t] *)
Inductive events : forall t : Time, schedule -> Prop :=
  | init : forall (t : Time) (r : RM), events t (add_sch t r vide)
  | add_eve :
      forall (t t' : Time) (r : RM),
      Tlt t' t ->
      forall l : schedule, events t' l -> events t (add_sch t r l).

Lemma events_add_eq :
 forall (t t' : Time) (r : RM) (l : schedule),
 events t (add_sch t' r l) -> t = t'.
intros.
inversion H; trivial.
Qed.

(*s Inductive principle for [events] *)
Lemma events_rec :
 forall P : Time -> schedule -> Set,
 (forall (t : Time) (r : RM), P t (add_sch t r vide)) ->
 (forall (t t' : Time) (r : RM),
  Tlt t' t ->
  forall l : schedule, events t' l -> P t' l -> P t (add_sch t r l)) ->
 forall (s : schedule) (t : Time), events t s -> P t s.
simple induction s.
intros t ev; absurd (events t vide); inversion ev.
simple destruct s0; intros.
rewrite <- events_add_eq with (1 := H2); trivial.
rewrite <- events_add_eq with (1 := H2); trivial.
apply H0 with t0.
inversion H2.
rewrite <- events_add_eq with (1 := H8); trivial.
inversion H2.
pattern t0 at 1 in |- *; rewrite <- events_add_eq with (1 := H8); trivial.
apply H1.
inversion H2.
pattern t0 at 1 in |- *; rewrite <- events_add_eq with (1 := H8); trivial.
Defined.

(* Properties of [events] *)
Lemma forall_eve_Tle :
 forall (t : Time) (l : schedule), events t l -> Tle_sch l t.
red in |- *; simple induction 1; intros; auto with time eve.
constructor; auto with time.
apply forall_incl_sch with (2 := H2); auto with time.
intros; apply Tle_trans with t'; auto with time.
Qed.

Lemma forall_eve_Tlt :
 forall (t t' : Time) (l : schedule), Tlt t t' -> events t l -> Tlt_sch l t'.
red in |- *; intros t t' l Hlt ev.
apply forall_incl_sch with (2 := forall_eve_Tle ev).
intros; apply Tle_lt_trans with t; trivial.
Qed.

Lemma first_time_eve_add :
 forall (t : Time) (l : schedule) (t' u : Time) (ru : RM),
 events t l -> first_time t' (add_sch u ru l) = first_time t l.
simple destruct 1; trivial.
Qed.
