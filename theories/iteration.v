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
  | h: _ ++ [_] = _ ++ [_] |- _ =>
      apply app_inj_tail in h; destruct h; simplify_eq
  | h : [] = snoc _ _ |- _ =>
      apply app_cons_not_nil in h; tauto
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
  | h: _ ++ [_] = _ ++ [_] |- _ =>
      apply app_inj_tail in h; destruct h; simplify_eq
  | h : [] = snoc _ _ |- _ =>
      apply app_cons_not_nil in h; tauto
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

Lemma invert_rev_eq_rev {A} :
  ∀ (xs ys : list A),
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
  | h: _ ++ [_] = _ ++ [_] |- _ =>
      apply app_inj_tail in h; destruct h; simplify_eq
  | h : [] = snoc _ _ |- _ =>
      apply app_cons_not_nil in h; tauto
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
      apply invert_rev_eq_rev in h;
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

Lemma snoc_inv {A} (xs xs0: list A) (x x0: A) :
  snoc xs x = snoc xs0 x0 ->
  xs = xs0 /\ x = x0.
Proof.
  intros Heq.
  rewrite <- (rev_involutive xs) in Heq.
  rewrite <- (rev_involutive xs0) in Heq.
  rewrite <- !rev_cons in Heq.
  simplify_list_eq. eauto.
Qed.

Local Ltac simplify_list_eq ::=
  repeat match goal with
  | h: _ ++ [_] = _ ++ [_] |- _ =>
      apply app_inj_tail in h; destruct h; simplify_eq
  | h : [] = snoc _ _ |- _ =>
      apply app_cons_not_nil in h; tauto
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
      apply invert_rev_eq_rev in h;
      simplify_eq
  | h: snoc _ _ = snoc _ _ |- _ =>
      apply snoc_inv in h;
      simplify_eq
  end.

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

Lemma steps_prefix {A} {α : nauto A} {i xs xs' s'} :
  steps α i xs' s' →
  xs ⊆ xs' →
  ∃ s, steps α i xs s.
Proof.
  unfold steps. induction 2; intros.
  { eauto. }
  { apply IHprefix in H. destruct H.
    apply rtcl_rtcl' in H. inversion H; simplify_list_eq.
    destruct H1; subst. (* TODO *)
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

Lemma invert_leadsto_snoc {A} (α : nauto A) xs x s' :
  leadsto α (snoc xs x) s' →
  ∃ s,
  leadsto α xs s ∧ step α s x s'.
Proof.
Admitted.

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
