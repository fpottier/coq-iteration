Require Import Utf8.
Require Import Coq.Program.Equality.
Require Import List. Import ListNotations.
Require Import stdpp.orders.
Set Primitive Projections.

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

Lemma snoc_inv {A} (xs xs0: list A) (x x0: A) :
  snoc xs x = snoc xs0 x0 ->
  xs = xs0 /\ x = x0.
Proof.
  intros. generalize dependent xs0.
  induction xs; unfold snoc; intros xs0 H; destruct xs0; simpl in *;
    try (simpl in *; inversion H; apply app_cons_not_nil in H2;
         contradiction).
  { inversion H. auto. }
  { inversion H. symmetry in H2. apply app_cons_not_nil in H2.
    contradiction. }
  { inversion H; subst. unfold snoc in *.
    destruct (IHxs _ H2). subst. auto. }
Qed.

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

Local Hint Resolve prefix_app : prefix.

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
  (simpl; eauto).

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

(* A definition of iteration spaces in terms of automata. *)

(* These are not necessarily finite-state automata. *)

Record automaton A := {
  state     : Type;
  initial   : state;
  step      : state → A → state → Prop;
  final     : state → Prop;
}.

Arguments state   {A} _.
Arguments initial {A} _.
Arguments step    {A} _.
Arguments final   {A} _.

Definition steps {A} (α : automaton A) : state α → list A → state α → Prop :=
  rtcl (step α).

(* -------------------------------------------------------------------------- *)

(* Similarity of automata. *)

(* [simulation α1 α2 R] means that the relation [R] is a simulation
   between the automata [α1] and [α2]. This implies that every sequence
   that is accepted by [α1] is also accepted by [α2]. *)

Inductive simulation {A}
  (α1 α2 : automaton A)
  (R : state α1 → state α2 → Prop)
: Prop :=
| Sim :
    R (initial α1) (initial α2) →
    (∀ s1 s2, final α1 s1 → R s1 s2 → final α2 s2) →
    (∀ s1 s2 a s'1,
      step α1 s1 a s'1 →
      R s1 s2 →
      ∃ s'2,
      step α2 s2 a s'2 ∧
      R s'1 s'2
    ) →
    simulation α1 α2 R.

(* TODO [simulation] could be a record?
   then the following lemmas would be the projections *)
Lemma init_simulation  {A} {α1 α2 : automaton A} {R} :
  simulation α1 α2 R →
  R (initial α1) (initial α2).
Proof.
  inversion 1; eauto.
Qed.

Local Ltac init_simulation :=
  match goal with
  Hsim: simulation ?α1 ?α2 ?R |- _ =>
    pose proof (init_simulation Hsim)
  end.

Lemma simulation_final  {A} {α1 α2 : automaton A} {R} :
  simulation α1 α2 R →
  ∀ s1 s2, final α1 s1 → R s1 s2 → final α2 s2.
Proof.
  inversion 1; eauto.
Qed.

Lemma step_simulation_diagram {A} {α1 α2 : automaton A} {R s1 s'1 s2 a} :
  simulation α1 α2 R →
  step α1 s1 a s'1 →
  R s1 s2 →
  ∃ s'2,
  step α2 s2 a s'2 ∧
  R s'1 s'2.
Proof.
  inversion 1; eauto.
Qed.

Local Ltac step_simulation_diagram s :=
  match goal with
  Hsim: simulation ?α1 ?α2 ?R,
  Hstep: step ?α1 ?s1 ?a ?s'1,
  HR : ?R ?s1 ?s2 |- _ =>
    let Hstep' := fresh Hstep in
    let HR' := fresh HR in
    pose proof (step_simulation_diagram Hsim Hstep HR)
      as (s & Hstep' & HR');
    clear Hstep HR;
    rename Hstep' into Hstep; rename HR' into HR
  end.

Lemma steps_simulation_diagram {A} {α1 α2 : automaton A} {R s1 s'1 xs} :
  simulation α1 α2 R →
  steps α1 s1 xs s'1 →
  ∀ {s2},
  R s1 s2 →
  ∃ s'2,
  steps α2 s2 xs s'2 ∧
  R s'1 s'2.
Proof.
  unfold steps. induction 2; intros.
  { eauto with rtcl. }
  { step_simulation_diagram s'2.
    edestruct IHrtcl as (s''2 & ? & ?); [ eauto |].
    eauto with rtcl. }
Qed.

Local Ltac steps_simulation_diagram s :=
  match goal with
  Hsim: simulation ?α1 ?α2 ?R,
  Hsteps: steps ?α1 ?s1 ?xs ?s'1,
  HR : ?R ?s1 ?s2 |- _ =>
    let Hsteps' := fresh Hsteps in
    let HR' := fresh HR in
    pose proof (steps_simulation_diagram Hsim Hsteps HR)
      as (s & Hsteps' & HR');
    clear Hsteps HR;
    rename Hsteps' into Hsteps; rename HR' into HR
  end.

(* [similar α1 α2] holds if there exists a simulation [R]
   between [α1] and [α2]. *)

Definition similar {A} (α1 α2 : automaton A) :=
  exists R, simulation α1 α2 R.

Local Infix "≼" := similar (at level 70, no associativity).

Lemma simulation_reflexive {A} (α : automaton A) :
  simulation α α eq.
Proof.
  econstructor; intros; subst; eauto.
Qed.

(* Composition of relations. *)
(* TODO is this already defined somewhere in stdlib or stdpp? *)
Definition compose {A B C} (R : A → B → Prop) (S : B → C → Prop) :=
  λ a c, ∃ b, R a b ∧ S b c.

Lemma simulation_transitive {A} (α β γ : automaton A) R S :
  simulation α β R →
  simulation β γ S →
  simulation α γ (compose R S).
Proof.
  inversion 1; inversion 1. unfold compose. econstructor.
  { eauto. }
  { firstorder. }
  { intros s1 s3 a s'1 Hstep (s2 & HR & HS).
    step_simulation_diagram s'2.
    step_simulation_diagram s'3.
    eauto. }
Qed.

(* -------------------------------------------------------------------------- *)

(* [s2a] converts an iteration space to an automaton. *)

(* This automaton is constructed in the simplest possible way. Its reachable
   states are the permitted lists of elements. Its edges form a tree, whose
   root (the automaton's initial state) is the empty list, and where every
   state other than the root has exactly one parent. *)

Definition s2a {A} (σ : space A) : automaton A :=
  {|
    state   := list A;
    initial := [];
    step xs x xs' := (snoc xs x = xs') ∧ permitted σ xs';
    final   := complete σ
  |}.

(* -------------------------------------------------------------------------- *)

(* [a2s] converts an automaton to an iteration space. *)

Program Definition a2s {A} (α : automaton A) : space A :=
  {|
    permitted xs := ∃ s, steps α (initial α) xs s;
    complete  xs := ∃ s, steps α (initial α) xs s ∧ final α s;
  |}.
Next Obligation.
  unfold steps. eauto with rtcl.
Qed.
Next Obligation.
  unfold steps. induction 2; intros.
  { eauto. }
  { apply IHprefix in H. destruct H.
    apply rtcl_rtcl' in H. inversion H.
    { unfold snoc in H3. apply app_cons_not_nil in H3.
      contradiction. }
    { apply snoc_inv in H1. destruct H1; subst.
      exists s2. apply rtcl'_rtcl. auto. } }
Qed.
Next Obligation.
  firstorder.
Qed.

(* -------------------------------------------------------------------------- *)

(* TODO clean up *)

Lemma foo {A} (σ : space A) :
  let α := s2a σ in
  ∀ xs s,
  steps α (initial α) xs s →
  s = xs.
Proof.
Admitted.

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

Lemma roundtrip1l {A} (σ : space A) :
  a2s (s2a σ) ⊑ σ.
Proof.
  unfold a2s. econstructor; simpl; intros xs.

  (* Inclusion of the [permitted] components. *)
  (* Goal: if in the automaton, out of the initial state, there is
     a path labeled [xs], then [xs] is permitted. *)
  { intros (s & Hsteps).
    assert (s = xs); [| subst s ].
    { eapply foo. exact Hsteps. }
    (* Either this path is empty, or it ends with an edge. *)
    apply rtcl_rtcl' in Hsteps. dependent destruction Hsteps.
    (* Case: the path is empty. *)
    { eapply permitted_empty. }
    (* Case: the path ends with an edge. *)
    { clear Hsteps. eauto using edge_target_is_permitted. }
  }

  (* Inclusion of the [complete] components. *)
  (* Goal: if in the automaton, out of the initial state, there is
     a path labeled [xs] to a final state, then [xs] is complete. *)
  { intros (s & Hsteps & ?).
    assert (s = xs); [| subst s ].
    { eapply foo. exact Hsteps. }
    tauto. }
Qed.

Lemma roundtrip1r {A} (σ : space A) :
  σ ⊑ a2s (s2a σ).
Proof.
  unfold a2s. econstructor; simpl; intros xs.

  (* Inclusion of the [permitted] components. *)
  (* Goal: if [xs] is permitted, then in the automaton, out of the
     initial state, there is a path labeled [xs]. *)
  { eauto using steps_self. }

  (* Inclusion of the [complete] components. *)
  (* Goal: if [xs] is complete then, in the automaton, out of the
     initial state, there is a path labeled [xs] to a final state. *)
  { eauto using steps_self, complete_permitted. }
Qed.

Lemma roundtrip1 {A} (σ : space A) :
  a2s (s2a σ) ≡ σ.
Proof.
  split; eauto using roundtrip1l, roundtrip1r.
Qed.

(* -------------------------------------------------------------------------- *)

(* Similarity is sound: [α1 ≼ α2] implies [a2s α1 ⊑ a2s α2]. That is, if
   [α1] is simulated by [α2] then the sequences accepted by [α1] form a
   subset of the sequences accepted by [α2]. *)

Lemma similar_subspace {A} (α1 α2 : automaton A) :
  α1 ≼ α2 →
  a2s α1 ⊑ a2s α2.
Proof.
  unfold similar. intros (R & Hsim).
  unfold subspace. split.
  { unfold permitted, a2s. intros xs (s1 & ?).
    init_simulation. steps_simulation_diagram s2.
    eauto. }
  { unfold complete, a2s.  intros xs (s1 & ? & ?).
    init_simulation. steps_simulation_diagram s2.
    eauto using simulation_final. }
Qed.

(* -------------------------------------------------------------------------- *)

Module SpaceNotations.
  Infix "⊑" := subspace (at level 70, no associativity).
  Infix "≡" := eqspace (at level 70, no associativity).
  Infix "≼" := similar (at level 70, no associativity).
End SpaceNotations.
