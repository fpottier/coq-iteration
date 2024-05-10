Require Import Utf8.
Require Import Coq.Program.Equality.
Require Import List. Import ListNotations.
Require Import stdpp.orders.

(* -------------------------------------------------------------------------- *)

(* TODO split this part into listSnoc.v *)

(* The [snoc] function on lists. *)

(* TODO need infix notation for snoc *)

Lemma cons_is_app {A} x (xs : list A) :
  x :: xs = [x] ++ xs.
Proof.
  reflexivity.
Qed.

Definition snoc {A} (xs : list A) (x : A) :=
  xs ++ [x].

(* TODO can we find an elegant way of incrementally extending the tactic
        [simplify_list_eq] as we go? use type classes? *)

Local Ltac simplify_list_eq :=
  repeat match goal with
  | h: snoc _ _ = snoc _ _ |- _ =>
      unfold snoc in h
  | h : [] = snoc _ _ |- _ =>
      unfold snoc in h
  | h : snoc _ _ = [] |- _ =>
      unfold snoc in h
  | h: _ ++ [_] = _ ++ [_] |- _ =>
      apply app_inj_tail in h; destruct h as (? & ?); simplify_eq
  | h : [] = _ ++ _ :: _ |- _ =>
      apply app_cons_not_nil in h; tauto
  | h : _ ++ _ :: _ = [] |- _ =>
      symmetry in h
  end.

Lemma invert_rev_eq_nil {A} (xs : list A) :
  rev xs = [] →
  xs = [].
Proof.
  destruct xs as [| x xs ]; simpl; intros; simplify_list_eq; eauto.
Qed.

Local Ltac simplify_list_eq ::=
  repeat match goal with
  | h: snoc _ _ = snoc _ _ |- _ =>
      unfold snoc in h
  | h : [] = snoc _ _ |- _ =>
      unfold snoc in h
  | h : snoc _ _ = [] |- _ =>
      unfold snoc in h
  | h: _ ++ [_] = _ ++ [_] |- _ =>
      apply app_inj_tail in h; destruct h as (? & ?); simplify_eq
  | h : [] = _ ++ _ :: _ |- _ =>
      apply app_cons_not_nil in h; tauto
  | h : _ ++ _ :: _ = [] |- _ =>
      symmetry in h
  | h: rev ?xs = [] |- _ =>
      apply invert_rev_eq_nil in h;
      simplify_eq
  | h: [] = rev ?xs |- _ =>
      symmetry in h
  end.

Lemma rev_injective {A} :
  ∀ xs ys : list A,
  rev xs = rev ys →
  xs = ys.
Proof.
  induction xs as [| x xs ]; simpl; intros ys ?.
  { simplify_list_eq. eauto. }
  destruct ys as [| y ys ]; simpl in *; simplify_list_eq.
  f_equal; eauto.
Qed.

Local Ltac simplify_list_eq ::=
  repeat match goal with
  | h: snoc _ _ = snoc _ _ |- _ =>
      unfold snoc in h
  | h : [] = snoc _ _ |- _ =>
      unfold snoc in h
  | h : snoc _ _ = [] |- _ =>
      unfold snoc in h
  | h: _ ++ [_] = _ ++ [_] |- _ =>
      apply app_inj_tail in h; destruct h as (? & ?); simplify_eq
  | h : [] = _ ++ _ :: _ |- _ =>
      apply app_cons_not_nil in h; tauto
  | h : _ ++ _ :: _ = [] |- _ =>
      symmetry in h
  | h: rev ?xs = [] |- _ =>
      apply invert_rev_eq_nil in h;
      simplify_eq
  | h: [] = rev ?xs |- _ =>
      symmetry in h
  | h: rev ?xs = rev ?ys |- _ =>
      apply rev_injective in h;
      simplify_eq
  end.

Lemma rev_cons {A} (xs : list A) (x : A) :
  rev (x :: xs) = snoc (rev xs) x.
Proof.
  reflexivity.
Qed.

Lemma rev_snoc {A} (xs : list A) (x : A) :
  rev (snoc xs x) = x :: rev xs.
Proof.
  unfold snoc. rewrite rev_app_distr. reflexivity.
Qed.

Lemma app_cons_eq_snoc_app {A} (xs ys : list A) y :
  xs ++ y :: ys  = snoc xs y ++ ys.
Proof.
  unfold snoc. rewrite <- app_assoc. reflexivity.
Qed.

Lemma qwd {A} (xs : list A) x y :
  x :: snoc xs y = snoc (x :: xs) y.
Proof.
  unfold snoc. rewrite (cons_is_app x xs), <- app_assoc. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* TODO split this part into listPrefix.v *)

(* The [prefix] relation on lists. *)

Inductive prefix {A} : list A → list A → Prop :=
| PrefixZero:
    ∀ xs,
    prefix xs xs
| PrefixSucc:
    ∀ xs x zs,
    prefix (snoc xs x) zs →
    prefix xs zs.

Global Hint Constructors prefix : prefix.

Module PrefixNotations.
  Infix "⊆" := prefix (at level 70, no associativity).
End PrefixNotations.
Import PrefixNotations.

Lemma prefix_transitive {A} (xs ys : list A) :
  xs ⊆ ys →
  ∀ zs,
  ys ⊆ zs →
  xs ⊆ zs.
Proof.
  induction 1; intros; eauto with prefix.
Qed.

Lemma prefix_snoc {A} (xs : list A) x :
  xs ⊆ snoc xs x.
Proof.
  eauto with prefix.
Qed.

Lemma prefix_app {A} :
  ∀ ys xs : list A,
  xs ⊆ xs ++ ys.
Proof.
  induction ys; intros;
  rewrite ?app_nil_r, ?app_cons_eq_snoc_app;
  eauto with prefix.
Qed.

Lemma prefix_singleton {A} :
  forall x : A,
  nil ⊆ [x].
Proof.
  intros x. change [x] with (snoc [] x). eauto with prefix.
Qed.

Lemma nil_prefix {A} :
  forall xs : list A,
  [] ⊆ xs.
Proof.
  intros xs. destruct xs as [| x xs']; eauto with prefix.
  change (x :: xs') with ([x] ++ xs').
  eauto using prefix_app, prefix_transitive.
Qed.

Lemma prefix_len {A} :
  forall l xs : list A,
    xs ⊆ l -> length xs <= length l.
  intros.
  induction H as [|xs' x l H Ih].
  - auto.
  - unfold snoc in Ih. rewrite app_length in Ih.
    simpl in Ih. lia.
Qed.
(* TODO : change two lemma names with invert *)
Lemma prefix_nil {A} :
  forall xs : list A,
  xs ⊆ [] ->
  xs = [].
Proof.
  intros xs H.
  apply prefix_len in H.
  simpl in H.
  apply Arith_prebase.le_n_0_eq_stt in H.
  symmetry in H.
  apply length_zero_iff_nil in H.
  auto.
Qed.

Lemma prefix_single {A} :
  forall xs (x : A),
    xs ⊆ [x] ->
    xs = [] \/ xs = [x].
Proof.
  intros xs x H.
  destruct xs as [|x' xs].
  left. auto.
  destruct xs.
  right. inversion H; subst. auto.
  apply prefix_len in H0.
  simpl in H0. lia.
  apply prefix_len in H. simpl in *. lia.
Qed.
Local Hint Resolve prefix_app prefix_transitive nil_prefix prefix_nil : prefix.

(* -------------------------------------------------------------------------- *)

(* TODO split this part *)

(* The reflexive-transitive closure of a labeled transition relation. *)

Inductive rtcl {S A} (R : S → A → S → Prop) : S → list A → S → Prop :=
| RtclNil:
    ∀ s,
    rtcl R s [] s
| RtclCons:
    ∀ s1 s2 s3 x xs,
    R s1 x s2 →
    rtcl R s2 xs s3 →
    rtcl R s1 (x :: xs) s3
.

Global Hint Constructors rtcl : rtcl.

Lemma rtcl_snoc {S A} (R : S → A → S → Prop) :
  ∀ s1 s2 s3 x xs,
  rtcl R s1 xs s2 →
  R s2 x s3 →
  rtcl R s1 (snoc xs x) s3.
Proof.
  induction 1; unfold snoc; simpl; eauto with rtcl.
Qed.

Global Hint Resolve rtcl_snoc : rtcl.

Inductive rtcl' {S A} (R : S → A → S → Prop) : S → list A → S → Prop :=
| Rtcl'Nil:
    ∀ s,
    rtcl' R s [] s
| Rtcl'Cons:
    ∀ s1 s2 s3 x xs,
    rtcl' R s1 xs s2 →
    R s2 x s3 →
    rtcl' R s1 (snoc xs x) s3
.

Global Hint Constructors rtcl' : rtcl'.

Lemma rtcl'_cons {S A} (R : S → A → S → Prop) :
  ∀ s2 xs s3,
  rtcl' R s2 xs s3 →
  ∀ s1 x,
  R s1 x s2 →
  rtcl' R s1 (x :: xs) s3.
Proof.
  induction 1; simpl; intros.
  { change [x] with (snoc [] x). eauto with rtcl'. }
  { rewrite qwd. eauto with rtcl'. }
Qed.

Global Hint Resolve rtcl'_cons : rtcl'.

Lemma rtcl_rtcl' {S A} (R : S → A → S → Prop) :
  ∀ s xs s',
  rtcl R s xs s' →
  rtcl' R s xs s'.
Proof.
  induction 1; simpl; eauto with rtcl'.
Qed.

Lemma rtcl'_rtcl {S A} (R : S → A → S → Prop) :
  ∀ s xs s',
  rtcl' R s xs s' →
  rtcl R s xs s'.
Proof.
  induction 1; simpl; eauto with rtcl.
Qed.

(* -------------------------------------------------------------------------- *)

(* TODO unused; throw away? *)

Definition mirror {S A} (R : S → A → S → Prop) : S → A → S → Prop :=
  λ s a s', R s' a s.

Lemma mirror_mirror {S A} (R : S → A → S → Prop) :
  mirror (mirror R) = R.
Proof.
  reflexivity.
Qed.

Lemma rtcl_mirror {S A} (R : S → A → S → Prop) :
  ∀ s xs s',
  rtcl R s xs s' →
  rtcl (mirror R) s' (rev xs) s.
Proof.
  induction 1; rewrite ?rev_cons; eauto with rtcl.
Qed.

(* -------------------------------------------------------------------------- *)

(* A definition of iteration spaces in terms of two predicates
   [permitted] and [complete], following Pereira and Filliâtre. *)

(* TODO comment, clean up, etc. *)

Record space A := {
  permitted : list A → Prop;
  complete  : list A → Prop;
  permitted_empty : permitted [];
  permitted_closed : ∀ xs zs, permitted zs → xs ⊆ zs → permitted xs;
  complete_permitted : ∀ xs, complete xs → permitted xs;
}.

Local Obligation Tactic :=
  (simpl; intros; eauto).

Arguments permitted {A} _.
Arguments complete  {A} _.

Definition subspace {A} (σ1 σ2 : space A) :=
  (∀ xs, permitted σ1 xs → permitted σ2 xs) ∧
  (∀ xs, complete σ1 xs → complete σ2 xs).

Local Infix "⊑" := subspace (at level 70, no associativity).

Global Instance subspace_reflexive : ∀ A, Reflexive (@subspace A).
Proof. econstructor; eauto. Qed.

Global Instance subspace_transitive : ∀ A, Transitive (@subspace A).
Proof. unfold subspace. econstructor; intuition eauto. Qed.

Definition eqspace {A} (σ1 σ2 : space A) :=
  σ1 ⊑ σ2 ∧ σ2 ⊑ σ1.

Local Infix "≡" := eqspace (at level 70, no associativity).

Program Definition top {A} : space A :=
  {| permitted xs := True; complete xs := True |}.

(* -------------------------------------------------------------------------- *)

(* A definition of iteration spaces in terms of non-deterministic automata. *)

(* These are not necessarily finite-state automata. *)

Record nauto A := {
  state          : Type;
  initial        : state → Prop;
  step           : state → A → state → Prop;
  final          : state → Prop;
  initial_exists : ∃ i, initial i;
}.

Arguments state          {A} _.
Arguments initial        {A} _.
Arguments step           {A} _.
Arguments final          {A} _.
Arguments initial_exists {A} _.

Ltac initial_exists i :=
  match goal with α: nauto _ |- _ =>
    pose proof (initial_exists α) as (i & ?)
  end.

Definition steps {A} (α : nauto A) : state α → list A → state α → Prop :=
  rtcl (step α).

(* Trivial properties of [steps]. *)

Lemma steps_nil {A} (α : nauto A) s :
  steps α s [] s.
Proof.
  unfold steps. eauto with rtcl.
Qed.

Lemma steps_cons {A} (α : nauto A) s1 s2 s3 x xs :
  step α s1 x s2 →
  steps α s2 xs s3 →
  steps α s1 (x :: xs) s3.
Proof.
  unfold steps. eauto with rtcl.
Qed.

Lemma steps_snoc {A} (α : nauto A) s1 s2 s3 x xs :
  steps α s1 xs s2 →
  step α s2 x s3 →
  steps α s1 (snoc xs x) s3.
Proof.
  unfold steps. eauto with rtcl.
Qed.

Global Hint Resolve steps_nil steps_cons steps_snoc : steps.

Lemma steps_rtlc' {A} (α : nauto A) i s xs :
  steps α i xs s ->
  rtcl' (step α) i xs s.
Proof. eauto using rtcl_rtcl'. Qed.

Lemma rtlc'_steps {A} (α : nauto A) i s xs :
  rtcl' (step α) i xs s ->
  steps α i xs s.
Proof. apply rtcl'_rtcl. Qed.

Lemma steps_prefix {A} {α : nauto A} {i xs xs' s'} :
  steps α i xs' s' →
  xs ⊆ xs' →
  ∃ s, steps α i xs s.
Proof.
  unfold steps. induction 2; intros.
  { eauto. }
  { apply IHprefix in H. destruct H.
    apply rtcl_rtcl' in H. inversion H; simplify_list_eq.
    eauto using rtcl'_rtcl. }
Qed.

(* -------------------------------------------------------------------------- *)

Definition leadsto {A} (α : nauto A) :=
  λ xs s, ∃ i, initial α i ∧ steps α i xs s.

Lemma leadsto_initial {A} (α : nauto A) i :
  initial α i →
  leadsto α [] i.
Proof.
  unfold leadsto. eauto with steps.
Qed.

Lemma leadsto_snoc {A} (α : nauto A) s s' x xs :
  leadsto α xs s →
  step α s x s' →
  leadsto α (snoc xs x) s'.
Proof.
  unfold leadsto. intros (i & ? & ?) ?. eauto with steps.
Qed.

Global Hint Resolve leadsto_initial leadsto_snoc : leadsto.

Lemma rtlc'_leadsto {A} (α : nauto A) i xs s:
  initial α i ->
  rtcl' (step α) i xs s ->
  leadsto α xs s.
Proof.
  intros. unfold leadsto. exists i.
  split; [assumption | eauto using rtlc'_steps].
Qed.

Ltac simplify_steps_snoc :=
  match goal with
  | h: steps _ _ (snoc _ _ ) _ |- _ =>
      apply rtcl_rtcl' in h; inversion h; subst; simplify_list_eq
  end.

Lemma invert_leadsto_snoc {A} (α : nauto A) xs x s' :
  leadsto α (snoc xs x) s' →
  ∃ s,
  leadsto α xs s ∧ step α s x s'.
Proof.
  intros (i & ? & ?). simplify_steps_snoc.
  exists s2. eauto using rtlc'_leadsto.
Qed.

Lemma leadsto_prefix {A} (α : nauto A) xs xs' s' :
  leadsto α xs' s' →
  xs ⊆ xs' →
  ∃ s, leadsto α xs s.
Proof.
  unfold leadsto. intros (i & ? & Hsteps) Hprefix.
  pose proof (steps_prefix Hsteps Hprefix) as (s & ?).
  eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Similarity of automata. *)

(* [simulation α1 α2 R] means that the relation [R] is a simulation
   between the automata [α1] and [α2]. This implies that every sequence
   that can be produced by [α1] can also be produced by [α2]. *)

Record simulation {A}
  (α1 α2 : nauto A)
  (R : state α1 → state α2 → Prop)
: Prop :=
{
  init_simulation :
    ∀ s1,
    initial α1 s1 →
    ∃ s2,
    R s1 s2 ∧
    initial α2 s2
  ;

  step_simulation :
    ∀ s1 s2 x s'1,
    step α1 s1 x s'1 →
    R s1 s2 →
    ∃ s'2,
    step α2 s2 x s'2 ∧
    R s'1 s'2
  ;

  close_simulation :
    ∀ s1 s2,
    final α1 s1 →
    R s1 s2 →
    final α2 s2
  ;

}.

Arguments init_simulation  {A α1 α2 R} _ {s1} _.
Arguments step_simulation  {A α1 α2 R} _ {s1 s2 x s'1} _ _.
Arguments close_simulation {A α1 α2 R} _ {s1 s2} _ _.

Local Ltac init_simulation i2 :=
  match goal with
  Hsim: simulation ?α1 ?α2 ?R,
  Hinit: initial ?α1 ?i1 |- _ =>
    let Hinit' := fresh Hinit in
    pose proof (init_simulation Hsim Hinit) as (i2 & ? & Hinit')
  end.

Local Ltac step_simulation s :=
  match goal with
  Hsim: simulation ?α1 ?α2 ?R,
  Hstep: step ?α1 ?s1 ?a ?s'1,
  HR : ?R ?s1 ?s2 |- _ =>
    let Hstep' := fresh Hstep in
    let HR' := fresh HR in
    pose proof (step_simulation Hsim Hstep HR)
      as (s & Hstep' & HR');
    clear Hstep HR;
    rename Hstep' into Hstep; rename HR' into HR
  end.

Lemma steps_simulation {A} {α1 α2 : nauto A} {R s1 s'1 xs} :
  simulation α1 α2 R →
  steps α1 s1 xs s'1 →
  ∀ {s2},
  R s1 s2 →
  ∃ s'2,
  steps α2 s2 xs s'2 ∧
  R s'1 s'2.
Proof.
  induction 2; intros.
  { eauto with steps. }
  { step_simulation s'2.
    edestruct IHrtcl as (s''2 & ? & ?); [ eauto |].
    eauto with steps. }
Qed.

Local Ltac steps_simulation s :=
  match goal with
  Hsim: simulation ?α1 ?α2 ?R,
  Hsteps: steps ?α1 ?s1 ?xs ?s'1,
  HR : ?R ?s1 ?s2 |- _ =>
    let Hsteps' := fresh Hsteps in
    let HR' := fresh HR in
    pose proof (steps_simulation Hsim Hsteps HR)
      as (s & Hsteps' & HR');
    clear Hsteps HR;
    rename Hsteps' into Hsteps; rename HR' into HR
  end.

(* [similar α1 α2] holds if there exists a simulation [R]
   between [α1] and [α2]. *)

Definition similar {A} (α1 α2 : nauto A) :=
  exists R, simulation α1 α2 R.

Local Infix "≼" := similar (at level 70, no associativity).

Lemma simulation_reflexive {A} (α : nauto A) :
  simulation α α eq.
Proof.
  econstructor; intros; subst; eauto.
Qed.

(* Composition of relations. *)
(* TODO is this already defined somewhere in stdlib or stdpp? *)
Definition compose {A B C} (R : A → B → Prop) (S : B → C → Prop) :=
  λ a c, ∃ b, R a b ∧ S b c.

Lemma simulation_transitive {A} (α β γ : nauto A) R S :
  simulation α β R →
  simulation β γ S →
  simulation α γ (compose R S).
Proof.
  intros. unfold compose. econstructor.
  { intros i1 ?. init_simulation i2. init_simulation i3. eauto. }
  { intros s1 s3 x s'1 Hstep (s2 & HR & HS).
    step_simulation s'2. step_simulation s'3. eauto. }
  { firstorder. }
Qed.

Global Instance similar_reflexive : ∀ A, Reflexive (@similar A).
Proof. econstructor. eauto using simulation_reflexive. Qed.

Global Instance similar_transitive : ∀ A, Transitive (@similar A).
Proof. intros A α1 α2 α3 (R & ?) (S & ?).
       eexists. eauto using simulation_transitive. Qed.

(* -------------------------------------------------------------------------- *)

(* [s2a] converts an iteration space to an automaton. *)

(* This automaton is constructed in the simplest possible way. Its reachable
   states are the permitted lists of elements. Its edges form a tree, whose
   root (the automaton's initial state) is the empty list, and where every
   state other than the root has exactly one parent. *)

Program Definition s2a {A} (σ : space A) : nauto A :=
  {|
    state         := list A ;
    initial xs    := xs = [] ;
    step xs x xs' := (snoc xs x = xs') ∧ permitted σ xs' ;
    final xs      := complete σ xs ;
  |}.

(* -------------------------------------------------------------------------- *)

(* [a2s] converts an automaton to an iteration space. *)

Program Definition a2s {A} (α : nauto A) : space A :=
  {|
    permitted xs := ∃ s, leadsto α xs s ;
    complete  xs := ∃ f, leadsto α xs f ∧ final α f ;
  |}.

Next Obligation.
  initial_exists i. eauto with leadsto.
Qed.
Next Obligation.
  match goal with h: ∃ s, _ |- _ => destruct h end.
  eauto using leadsto_prefix.
Qed.
Next Obligation.
  firstorder.
Qed.

(* -------------------------------------------------------------------------- *)

(* TODO clean up *)

Local Lemma edge_target_is_permitted {A} (σ : space A) xs x xs' :
  step (s2a σ) xs x xs' →
  permitted σ xs'.
Proof.
  unfold s2a. simpl. tauto.
Qed.

Local Lemma steps_self_append {A} (σ : space A) :
  ∀ ys xs,
  permitted σ (xs ++ ys) →
  steps (s2a σ) xs ys (xs ++ ys).
Proof.
  induction ys as [| y ys ]; intros xs.
  { intros _.
    rewrite app_nil_r.
    unfold s2a, steps, step.
    eauto with rtcl. }
  { rewrite app_cons_eq_snoc_app.
    intros Hpermitted.
    econstructor; [| eapply IHys; eauto ].
    unfold s2a, step.
    split; [ reflexivity |].
    eapply permitted_closed; eauto with prefix. }
Qed.

Local Lemma steps_self {A} (σ : space A) :
  ∀ xs,
  permitted σ xs →
  steps (s2a σ) [] xs xs.
Proof.
  eauto using steps_self_append.
Qed.

(* -------------------------------------------------------------------------- *)

(* The lemma [roundtrip1] states that if an iteration space [σ] is
   first converted to an automaton, and if this automaton is then
   converted back to an iteration space, then the result is [σ]
   again, up to equivalence [≡]. *)

Lemma invert_leadsto_self {A} {σ : space A} {xs s} :
  leadsto (s2a σ) xs s →
  s = xs.
Proof.
Admitted.

Lemma leadsto_permitted {A} {σ : space A} xs s :
  leadsto (s2a σ) xs s →
  permitted σ xs.
Proof.
  intros Hleadsto.
  assert (s = xs) by eauto using invert_leadsto_self. subst s.
  (* Either this path is empty, or it ends with an edge. *)
  destruct Hleadsto as (i & Hinit & Hsteps).
  apply rtcl_rtcl' in Hsteps. dependent destruction Hsteps.
  (* Case: the path is empty. *)
  { eapply permitted_empty. }
  (* Case: the path ends with an edge. *)
  { clear Hsteps. eauto using edge_target_is_permitted. }
Qed.

Lemma leadsto_complete {A} {σ : space A} xs s :
  leadsto (s2a σ) xs s →
  complete σ s →
  complete σ xs.
Proof.
  intros Hleadsto.
  assert (s = xs) by eauto using invert_leadsto_self. subst s.
  eauto.
Qed.

Local Lemma leadsto_self {A} (σ : space A) :
  ∀ xs,
  permitted σ xs →
  leadsto (s2a σ) xs xs.
Proof.
  intros. exists []. split.
  { reflexivity. }
  { eauto using steps_self. }
Qed.

Lemma roundtrip1l {A} (σ : space A) :
  a2s (s2a σ) ⊑ σ.
Proof.
  unfold a2s. econstructor; simpl; intros xs.
  { intros (s & ?). eauto using leadsto_permitted. }
  { intros (f & ? & ?). eauto using leadsto_complete. }
Qed.

Lemma roundtrip1r {A} (σ : space A) :
  σ ⊑ a2s (s2a σ).
Proof.
  unfold a2s. econstructor; simpl; intros xs.
  { eauto using leadsto_self. }
  { eauto 7 using leadsto_self, complete_permitted. }
Qed.

Lemma roundtrip1 {A} (σ : space A) :
  a2s (s2a σ) ≡ σ.
Proof.
  split; eauto using roundtrip1l, roundtrip1r.
Qed.

(* -------------------------------------------------------------------------- *)

Definition functional {A B} (R : A → B → Prop) :=
  ∀ a b1 b2, R a b1 → R a b2 → b1 = b2.

Local Ltac functional R :=
  match goal with h1: R ?a ?b1, h2: R ?a ?b2 |- _ =>
    let Hfun := fresh in
    assert (Hfun: functional R) by eauto;
    pose proof (Hfun _ _ _ h1 h2);
    clear Hfun;
    simplify_eq
  end.

Definition innocent {A} (α : nauto A) :=
  functional (leadsto α).

Lemma roundtrip2l {A} (α : nauto A) :
  innocent α →
  s2a (a2s α) ≼ α.
Proof.
  unfold innocent. intro Hfun.
  unfold s2a, a2s; simpl.
  (* The state [xs] in the automaton [s2a (a2s α)] is simulated by
     state [s] in automaton [α] if and only if in the automaton [α]
     the path [xs] leads to the state [s]. In other words, the desired
     simulation is [leadsto α]. *)
  exists (leadsto α).
  econstructor; simpl.
  { initial_exists i. intros; subst; eauto with leadsto. }
  { intros xs s x ? (<- & (s' & Hs')) Hs.
    apply invert_leadsto_snoc in Hs'. destruct Hs' as (? & ? & ?).
    functional (leadsto α).
    eauto with leadsto. }
  { intros xs s (f & ? & ?) ?.
    functional (leadsto α).
    eauto. }
Qed.

Lemma roundtrip2r {A} (α : nauto A) :
  α ≼ s2a (a2s α).
Proof.
  unfold s2a, a2s; simpl.
  (* The state [s] in automaton [α] is simulated by the state [xs] in
     the automaton [s2a (a2s α)] if and only if in the automaton [α]
     the state [s] is reachable from some initial state [i] via a path
     labeled [xs]. In other words, the desired simulation is
     [flip (leadsto α)]. *)
  exists (flip (leadsto α)).
  econstructor; simpl; eauto 7 with leadsto.
Qed.

(* For [leadsto α] to be functional, the automaton [α] must have at
   most one initial state, and [step α] must be functional. These
   are necessary and sufficient conditions. *)

Lemma prove_innocent {A} (α : nauto A) :
  (∀ i1 i2, initial α i1 → initial α i2 → i1 = i2) →
  (functional (λ '(s, x) s', step α s x s')) →
  innocent α.
Proof.
Admitted.

(* The automaton produced by [s2a] is innocent. *)

Lemma s2a_innocent {A} (σ : space A) :
  innocent (s2a σ).
Proof.
  eapply prove_innocent; simpl.
  { congruence. }
  { intros [xs x] xs1 xs2 [? _] [? _]. congruence. }
Qed.

(* Thus, every automaton [α] is simulated by an innocent automaton [α'],
   which describes the same iteration space. *)

Lemma innocence_is_possible {A} (α : nauto A) :
  ∃ α',
  innocent α' ∧
  α ≼ α' ∧
  a2s α' ≡ a2s α.
Proof.
  exists (s2a (a2s α)). split; [| split ].
  { eauto using s2a_innocent. }
  { eauto using roundtrip2r. }
  { eauto using roundtrip1. }
Qed.

(* -------------------------------------------------------------------------- *)

(* Similarity is sound: [α1 ≼ α2] implies [a2s α1 ⊑ a2s α2]. That is, if
   [α1] is simulated by [α2] then the sequences produced by [α1] form a
   subset of the sequences produced by [α2]. *)

Lemma similar_subspace {A} (α1 α2 : nauto A) :
  α1 ≼ α2 →
  a2s α1 ⊑ a2s α2.
Proof.
  unfold similar. intros (R & Hsim).
  unfold subspace. split.
  { unfold permitted, a2s.
    intros xs (s1 & (i1 & ? & ?)). unfold leadsto.
    init_simulation i2. steps_simulation s2. eauto. }
  { unfold complete, a2s.
    intros xs (s1 & (i1 & ? & ?) & ?). unfold leadsto.
    init_simulation i2. steps_simulation s2. firstorder. }
Qed.

Lemma subspace_similar {A} (σ1 σ2 : space A) :
  σ1 ⊑ σ2 →
  s2a σ1 ≼ s2a σ2.
Proof.
  unfold subspace. intros (? & ?).
  (* The desired simulation relation is just equality. *)
  unfold similar. exists eq.
  econstructor; simpl; intros; subst; intuition eauto.
Qed.

(* -------------------------------------------------------------------------- *)

Module SpaceNotations.
  Infix "⊑" := subspace (at level 70, no associativity).
  Infix "≡" := eqspace (at level 70, no associativity).
  Infix "≼" := similar (at level 70, no associativity).
End SpaceNotations.

(* -------------------------------------------------------------------------- *)

Module EnumerateEmpty.
  
  Program Definition create_space : space unit :=
    {|
      permitted ys := ys = [] ;
      complete  ys := ys = [] ;
    |}.
  Next Obligation.
    subst.
    eauto using prefix_nil.
  Qed.

  Program Definition create_nauto : nauto unit :=
    {|
      state   := unit;
      initial := (fun _ => True) ;
      step    := (fun _ _ _ => False);
      final   := (fun _ => True);
    |}.
  Next Obligation.
    exists tt. auto.
  Qed.

  Lemma leads_to_empty :
    forall xs x,
      leadsto create_nauto xs x -> xs = [].
    Proof.
      intros.
      inversion H as [s [H1 H2]].
      inversion H2. auto. inversion H0.
    Qed.
    
  Lemma equiv :
    create_space ≡ a2s create_nauto.
  Proof.
    split.
    - split; simpl; intros; exists tt; try split; auto;
    unfold leadsto; exists tt; simpl; split; auto;
    subst; eauto with steps.
    - split; simpl; intros.
      + destruct H as [s H]. apply leads_to_empty with s. auto.
      + destruct H as [s [H1 H2]]. apply leads_to_empty with s. auto. 
  Qed.

End EnumerateEmpty.

Module EnumerateSingle.  

  Program Definition create_space {A} (x : A) : space A :=
    {|
      permitted ys := ys ⊆ [x];
      complete  ys := ys = [x];
    |}.
  Next Obligation.
    eauto with prefix.
  Qed.
  Next Obligation. 
    eauto with prefix.
  Qed.
  Next Obligation.
    subst. constructor.
  Qed.
  
  Program Definition create_nauto {A} (x : A) : nauto A :=
    {|
      state   := bool;
      initial := (fun s => s = true) ;
      step    := (fun s1 n s2 => n = x /\ s1=true /\ s2=false);
      final   := (fun s => s =false);
    |}.

  (* TODO check equiv with list-space *)

  Lemma nauto_true_empty :
    forall A (x:A) xs, leadsto (create_nauto x) xs true -> xs = [].
  Proof.
    intros A x xs H.
    inversion H as [s [H1 H2]].
    simpl in H1. subst. inversion H2.
    auto. subst. destruct H0 as [H3 [H4 H5]].
    subst. inversion H1. subst. inversion H0 as [_ [H7 _]]. discriminate.
  Qed.

  Lemma equiv :
    forall A (x:A), create_space x ≡ a2s (create_nauto x).
  Proof.
    intros. split; split; simpl; intros. 
    - apply prefix_single in H. destruct H.
      exists true. subst. apply leadsto_initial. simpl. auto.
      subst. exists false. replace ([x]) with (snoc [] x).
      apply leadsto_snoc with true. apply leadsto_initial. simpl. auto.
      simpl. split; auto. unfold snoc. auto.
    - exists false. split; auto.
      subst. replace ([x]) with (snoc [] x).
      apply leadsto_snoc with true.
      apply leadsto_initial. simpl. auto.
      simpl. split; auto. unfold snoc. auto.
    - destruct H as [s2 [s1 [H1 H2]]].
      inversion H2; subst. eauto with prefix.
      inversion H. subst. inversion H0. subst.
      eauto with prefix. inversion H3. subst. inversion H.
      destruct H10. destruct H7. subst. discriminate.
    - intros. simpl. inversion H as [s [H1 H2]].
      inversion H1 as [s2 [H3 H4]].
      simpl in *. inversion H4; subst. discriminate.
      simpl in *. subst.
      inversion H5. subst. destruct H0 as [H6]. rewrite H6. auto.
      subst. destruct H0 as [_ [_ H0]].
      destruct H2 as [_ [H2 _]]. subst. discriminate.
  Qed.
End EnumerateSingle.

(* Combinator for enumerating the elements of list [xs], in order. *)

(* TODO give a better name to this combinator *)
(* FIXME? should this combinator be a record? *)

Module EnumerateList.

  (* TODO change [create] to something more useful *)
  (* list_space ? *)
  (* maybe avoid [_space] everywhere *)
  (* maybe two modules: one for iteration spaces and other for automata *)
  Program Definition create_space {A} (xs: list A): space A :=
    {|
      permitted ys := ys ⊆ xs ;
      complete  ys := ys = xs ;
    |}.
  Next Obligation.
    eauto with prefix.
  Qed.
  Next Obligation.
    eauto with prefix.
  Qed.
  Next Obligation.
    subst xs0. constructor.
  Qed.

  Program Definition create_nauto {A} (xs: list A) : nauto A :=
    {|
      state   := list A;
      initial := (fun ys => ys = []) ;
      step    := (fun ys1 n ys2 =>
                    ys2 = snoc ys1 n /\ ys2 ⊆ xs ) ;
      final   := (fun ys => ys = xs);
    |}.
      
  Lemma list_equiv {A} :
    forall (xs: list A),
      (create_space xs) ⊑ a2s (create_nauto xs).
  Proof.
  Admitted.
End EnumerateList.

Module EnumerateRangeIncr.

  Inductive incr : nat -> list nat -> Prop :=
  |Incr_base : forall x,
      incr x []
  |Incr_prev : forall x l,
      incr x l -> incr x (snoc l (x +length l)).

  Lemma incr_prefix :
    forall l xs x,
      incr x l -> xs ⊆ l -> incr x xs.
    intros l xs x H1 H2.
    induction H2 as [|x' n l H3 H4]. auto.
    
    
  Program Definition create_space (i : nat) (j : nat) : space nat :=
    {|
      permitted ys :=
        i <= j -> length ys <= j /\ incr i ys;
      complete  ys :=
        i <= j -> length ys = j
      |}.
  Next Obligation.
    split. lia. constructor.
  Qed.
  Next Obligation.
    apply H in H1. destruct H1 as [H2 H3]. split.
    - apply prefix_len in H0. lia.
    - 
    
  Program Definition create_nauto (n1 : nat) (n2 : nat) : nauto nat :=
    {|
      state   := nat;
      initial := (fun s => s = n1) ;
      step    :=
        (fun s1 n s2 => n = s1 /\ s2 = n + 1 /\ s2 <= n2);
      final   := (fun s2 => s2 = n2);
    |}.

End EnumerateRangeIncr.

Module EnumerateInfiniteStream
.

  Inductive valid_seq {A} :
    list A -> (nat -> A) -> Prop :=
  |Valid_nil : forall f, valid_seq nil f
  |Valid_cons : forall l f,
      valid_seq l f ->
      valid_seq (snoc l (f (length l))) f.
  
  Program Definition create_space {A} (f: nat -> A) : space A := 
    {|
      permitted ys := valid_seq ys f;
      complete  ys := False;
    |}.
  Next Obligation.
    constructor.
  Qed.
  Next Obligation.
    Admitted.
  Next Obligation.
    inversion H.
  Qed.


  Program Definition create_nauto {A} (f: nat -> A) : nauto A :=
    {|
      state   := nat;
      initial := (fun s => s = 0) ;
      step    :=
        (fun s1 n s2 => s2 = s1 + 1 /\ n = f s1);
      final   := (fun _ => False);
    |}.
  
End EnumerateInfiniteStream.

Require TLC.LibSet.
Require TLC.LibList.
Require TLC.LibLogic.
Require TLC.LibMultiset.

Module EnumerateSet.
   Import TLC.LibSet.
   Import TLC.LibList.


  (* TODO change fun to set, maybe use functors *)
  Program Definition
    create_space {A} (E: A -> Prop) : space A := 
    {|
      permitted ys :=
        (* TODO : convert ys to set, check if subset *)
        noduplicates ys /\ forall x, mem x ys -> E x
    ;
      (* TODO : change to something else maybe? *)
      complete ys := list_repr_impl E ys;
    |}.
  Next Obligation.
    split.
    - constructor.
    - intros. inversion H.
  Qed.
  Next Obligation.
  Admitted.
  Next Obligation.
    split.
    inversion H. auto.
    intros. inversion H. apply H2 in H0. auto.
  Qed.

  Program Definition create_nauto {A} (E: A -> Prop) : nauto A :=
    {|
      state   := list A;
      initial := (fun s => s = nil) ;
      step    :=
        (fun s1 x s2 =>
           (~ mem x s1) /\ s2 = x::s1 /\ E x
        );
      final   := (fun s2 => list_repr_impl E s2);
    |}.
    
End EnumerateSet.


Module EnumerateMultiset.
   Import TLC.LibMultiset.
   Import TLC.LibList.
   Import TLC.LibLogic.

   Fixpoint incr {A} (l : list (A*nat)) (x : A) :=
     match l with
     |nil => (x, 1)::nil
     |(y, n)::t =>
        If y = x then
          (y, n+1)::t
        else
          (y, n)::(incr t x)
     end.
       
   Fixpoint zip {A} (l : list A) :=
     match l with
     |nil => nil
     |x::t =>
        incr (zip t) x end.
   
  Program Definition
    create_space {A} (E: A -> nat) : space A := 
    {|
      (* convert list to multiset *)
      permitted ys :=
        noduplicates (LibList.map (@fst _ _) (zip ys))
        /\ forall n x, mem (x,n) (zip ys) -> (n = E x /\ n > 0);
      
      complete  ys := list_repr_impl E (zip ys);
    |}.
  Next Obligation.
    split.
    - rewrite map_nil. constructor.
    - intros. inversion H.      
  Qed.
  Next Obligation.
  Admitted.
  Next Obligation.
    split.
    - inversion H. auto.
    - intros. inversion H.
      destruct H2 with n x.
      auto.
  Qed.

  Program Definition create_nauto {A} (E: A -> nat) : nauto A :=
    {|
      state   := list (A*nat);
      initial := (fun s => s = nil) ;
      step    :=
        (fun s1 x s2 =>
           (~ mem (x, E x) s1
            /\ s2 = incr s1 x /\ E x > 0))
        ;
      final := (fun s2 => list_repr_impl E s2);
    |}.
    
End EnumerateMultiset.




(* Combinator for enumerating the elements of list [xs], in order,
   expressed as an automaton. *)

(* Combinator for enumerating integers from [i] up to [j], expressed as an
   interation space. *)

(* TODO give a better name to this combinator *)
(* FIXME? should this combinator be a record? *)

(* Module EnumerateItoJ. *)
(*   (* TODO change later to Z *) *)
(*   Variable i : nat. *)
(*   Variable j : nat. *)

(*   Inductive walk : nat -> list nat -> Prop := *)
(*   | walk_done : forall x, *)
(*       walk x (x::[]) *)
(*   | walk_next : forall *)

(*   Definition create : (space nat) := *)
(*     {| permitted xs := |}. *)

(* End EnumerateItoJ. *)
