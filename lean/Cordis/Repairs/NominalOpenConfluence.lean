import Cordis.Repairs.NominalConfluence
import Cordis.Repairs.GuardedNameExtension

/-! Confluence for name-carrying codes with child commands. Two quiet open
histories with the same addressed input, of a renaming-equivariant program
whose births draw names fresh for the drawing code, end with tables that
agree up to a renaming. Retirements and removals of children are allowed,
so a removed child's name can be drawn again; freshness is what keeps such
a reuse out of the parent's code. `EquivariantReuseCounterexample` is the
matching failure when one draw is stale.
The comparisons are the repository's `compare_open_endpoints` and
`compare_surviving_endpoints`, and the reductions come from
`eliminate_closed_episodes`, all applied unchanged to the quotient program. -/
namespace Cordis.Repairs.NominalOpenConfluence
open Calculus Stages LegalHistory GuardedHistory
open PaperEffectEquations (CoeffectOperations)
open TypedRegistry (encodeProgram)
open GuardedBirthAddresses (Addressed AddressedCommand)
universe u
variable {Name Key Code : Type u} {V : Key → Type u} {ops : CoeffectOperations V}
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

section Transport
variable {Value Code' Error : Type u} {f : Code → Code'}
variable {program : Code → Stages.Instruction Name Key Value Code Error}
variable {program' : Code' → Stages.Instruction Name Key Value Code' Error}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error

theorem viewAt_registry (r : R) (name : Name) :
    ControlFrame.viewAt (CodeMap.registry f r) name = ControlFrame.viewAt r name := by
  unfold ControlFrame.viewAt
  cases h : r name <;> simp [h]

variable (compatible : CodeMap.Compatible f program program') {last : Nat}

/-- An episode of the image history is an episode of the source. -/
def closedEpisode_back (trace : Trace program last) draws
    (episode : ClosedEpisode (CodeMap.mapTrace compatible trace draws)) :
    ClosedEpisode trace where
  name := episode.name
  opened := episode.opened
  closed := episode.closed
  interval :=
    { positive := episode.interval.positive
      ordered := episode.interval.ordered
      bounded := episode.interval.bounded
      installed := fun t lower upper => by
        have known := episode.interval.installed t lower upper
        change ControlFrame.viewAt (CodeMap.registry f (trace.state t)) episode.name ≠ none at known
        rwa [viewAt_registry] at known
      before := by
        have known := episode.interval.before
        change ControlFrame.viewAt (CodeMap.registry f (trace.state _)) episode.name = none at known
        rwa [viewAt_registry] at known
      after := by
        have known := episode.interval.after
        change ControlFrame.viewAt (CodeMap.registry f (trace.state _)) episode.name = none at known
        rwa [viewAt_registry] at known }

theorem open_map (trace : Trace program last) draws
    (isOpen : ¬ Nonempty (ClosedEpisode trace)) :
    ¬ Nonempty (ClosedEpisode (CodeMap.mapTrace compatible trace draws)) :=
  fun ⟨episode⟩ => isOpen ⟨closedEpisode_back compatible trace draws episode⟩

theorem isRootInsertion_map (trace : Trace program last) draws :
    GuardedBirthAddresses.isRootInsertion (CodeMap.mapTrace compatible trace draws) =
      GuardedBirthAddresses.isRootInsertion trace := by
  funext time
  unfold GuardedBirthAddresses.isRootInsertion
  change (match CodeMap.event f (trace.event time) with
    | .command (.insert _ _) => true | _ => false) = _
  cases trace.event time with
  | command c => cases c <;> rfl
  | lifecycle => rfl

theorem rule_map (trace : Trace program last) draws (time : Nat) :
    (CodeMap.mapTrace compatible trace draws).rule time = trace.rule time :=
  CodeMap.eventRule_event _

theorem actor_map (trace : Trace program last) draws (time : Nat) :
    (CodeMap.mapTrace compatible trace draws).actor time = trace.actor time :=
  CodeMap.eventActor_event _

theorem isParentStage_map (trace : Trace program last) draws (parentBirth : Nat) :
    GuardedBirthAddresses.isParentStage (CodeMap.mapTrace compatible trace draws) parentBirth =
      GuardedBirthAddresses.isParentStage trace parentBirth := by
  funext time
  unfold GuardedBirthAddresses.isParentStage
  rw [rule_map, actor_map]
  rfl

theorem addressed_map (trace : Trace program last) draws {birth : Nat} {address : GuardedBirthAddresses.Address} :
    Addressed (CodeMap.mapTrace compatible trace draws) birth address ↔ Addressed trace birth address := by
  constructor
  · intro born
    induction born with
    | @root time name c bounded event =>
      rw [isRootInsertion_map]
      change CodeMap.event f (trace.event time) = _ at event
      cases original : trace.event time with
      | lifecycle => rw [original] at event; cases event
      | command cmd =>
        rw [original] at event
        cases cmd with
        | insert name' c' => exact Addressed.root (name := name') (component := c') bounded original
        | retire => cases event
        | remove => cases event
    | @child time parentBirth name parentAddress bounded births vacant present tag parent ih =>
      rw [isParentStage_map]
      refine Addressed.child (name := name) bounded ?_ ?_ ?_ ?_ ih
      · rwa [rule_map] at births
      · change CodeMap.registry f (trace.state time) name = none at vacant
        simpa using vacant
      · change CodeMap.registry f (trace.state (time + 1)) name ≠ none at present
        simpa using present
      · rwa [actor_map] at tag
  · intro born
    induction born with
    | @root time name c bounded event =>
      rw [← isRootInsertion_map compatible trace draws]
      exact Addressed.root (name := name) (component := CodeMap.component f c) bounded
        (show CodeMap.event f (trace.event time) = _ by rw [event]; rfl)
    | @child time parentBirth name parentAddress bounded births vacant present tag parent ih =>
      rw [← isParentStage_map compatible trace draws]
      refine Addressed.child (name := name) bounded ?_ ?_ ?_ ?_ ih
      · rwa [rule_map]
      · change CodeMap.registry f (trace.state time) name = none
        simpa using vacant
      · change CodeMap.registry f (trace.state (time + 1)) name ≠ none
        simpa using present
      · rwa [actor_map]

theorem addressOf_map (trace : Trace program last) draws (birth : Nat) :
    GuardedBirthAddresses.addressOf (CodeMap.mapTrace compatible trace draws) birth =
      GuardedBirthAddresses.addressOf trace birth := by
  cases known : GuardedBirthAddresses.addressOf trace birth with
  | some address =>
    exact (GuardedBirthAddresses.addressOf_eq_some _).mpr
      ((addressed_map compatible trace draws).mpr ((GuardedBirthAddresses.addressOf_eq_some _).mp known))
  | none =>
    cases mapped : GuardedBirthAddresses.addressOf (CodeMap.mapTrace compatible trace draws) birth with
    | none => rfl
    | some address =>
      have back := (addressed_map compatible trace draws).mp ((GuardedBirthAddresses.addressOf_eq_some _).mp mapped)
      rw [(GuardedBirthAddresses.addressOf_eq_some _).mpr back] at known
      cases known

def addressedCommand : AddressedCommand Name Key Code → AddressedCommand Name Key Code'
  | .insert name c => .insert name (CodeMap.component f c)
  | .retire target c => .retire target (CodeMap.component f c)
  | .remove target c => .remove target (CodeMap.component f c)

theorem targetAt_map (trace : Trace program last) draws (time : Nat) (name : Name) :
    GuardedBirthAddresses.targetAt (CodeMap.mapTrace compatible trace draws) time name =
      (GuardedBirthAddresses.targetAt trace time name).map (fun target => (target.1, CodeMap.component f target.2)) := by
  unfold GuardedBirthAddresses.targetAt
  change ((trace.notes time).1 name).bind (fun birth =>
    (GuardedBirthAddresses.addressOf (CodeMap.mapTrace compatible trace draws) birth).bind fun address =>
      (CodeMap.registry f (trace.state time) name).bind fun row => some (address, row.component)) = _
  cases (trace.notes time).1 name with
  | none => rfl
  | some birth =>
    simp only [Option.bind_some, addressOf_map]
    cases GuardedBirthAddresses.addressOf trace birth with
    | none => rfl
    | some address =>
      simp only [Option.bind_some]
      cases h : trace.state time name <;> simp [h]

theorem commandAt_map (trace : Trace program last) draws (time : Nat) :
    GuardedBirthAddresses.commandAt (CodeMap.mapTrace compatible trace draws) time =
      (GuardedBirthAddresses.commandAt trace time).map (addressedCommand (f := f)) := by
  unfold GuardedBirthAddresses.commandAt
  have mapped : (CodeMap.mapTrace compatible trace draws).event time = CodeMap.event f (trace.event time) := rfl
  rw [mapped]
  cases trace.event time with
  | lifecycle => rfl
  | command c =>
    cases c with
    | insert => rfl
    | retire name =>
      simp only [CodeMap.event, CodeMap.command, targetAt_map, Option.map_map]
      rfl
    | remove name =>
      simp only [CodeMap.event, CodeMap.command, targetAt_map, Option.map_map]
      rfl

theorem orchestrationInput_map (trace : Trace program last) draws :
    GuardedBirthAddresses.orchestrationInput (CodeMap.mapTrace compatible trace draws) =
      (GuardedBirthAddresses.orchestrationInput trace).map (addressedCommand (f := f)) := by
  unfold GuardedBirthAddresses.orchestrationInput
  rw [List.map_filterMap]
  congr 1
  funext time
  exact commandAt_map compatible trace draws time

end Transport

/-- Open-history confluence for name-carrying codes, with child commands.
Two quiet histories without closed episodes, with the same addressed
input, of a renaming-equivariant program whose every birth draws a name
the parent's code does not mention, end with tables that agree up to a
renaming of their owners. -/
theorem nominal_open_confluence {program : Code → TypedRegistry.Instruction Name ops Code}
    (N : NominalConfluence.Nominal program) {last rightLength : Nat}
    (left : Trace (encodeProgram program) last) (right : Trace (encodeProgram program) rightLength)
    (leftFresh : NominalConfluence.DrawsFresh N left) (rightFresh : NominalConfluence.DrawsFresh N right)
    (leftOpen : ¬ Nonempty (ClosedEpisode left))
    (rightOpen : ¬ Nonempty (ClosedEpisode right))
    (leftQuiet : Progress.Quiet (left.state last)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (input : GuardedBirthAddresses.orchestrationInput left = GuardedBirthAddresses.orchestrationInput right)
    (observe : ∀ key, Setoid (V key)) (contracts : GuardedCanonicalSchedule.OperationContracts ops observe) :
    ∃ p : Renaming.Permutation Name, ∀ name key, Iterators.OptionRel (TypedCoeffectReplay.setoid observe).r
      (StageRecovery.tableAt (left.state last) name key)
      (StageRecovery.tableAt (right.state rightLength) (p.toFun name) key) := by
  let compatible := NominalConfluence.compatible N
  let first := CodeMap.mapTrace compatible left (NominalConfluence.draws_agree N leftFresh)
  let second := CodeMap.mapTrace compatible right (NominalConfluence.draws_agree N rightFresh)
  have compared := GuardedNameExtension.compare_open_endpoints first second
    (open_map compatible left _ leftOpen) (NominalConfluence.quiet_registry leftQuiet)
    (open_map compatible right _ rightOpen) (NominalConfluence.quiet_registry rightQuiet)
    (NominalConfluence.quotient_child_continuations N)
    (by rw [orchestrationInput_map, orchestrationInput_map, input]) observe
    contracts.recovery contracts.commutative contracts.respect
  obtain ⟨_, ⟨p, related⟩, _⟩ := compared
  have agreement : GuardedConfluence.EndpointAgreement observe (first.state last) (second.state rightLength) :=
    ⟨p, _, _, .refl _, .refl _, related⟩
  obtain ⟨q, tables⟩ := agreement.tables observe
  refine ⟨q, fun name key => ?_⟩
  have known := tables name key
  change Iterators.OptionRel _ (StageRecovery.tableAt (CodeMap.registry _ (left.state last)) name key)
    (StageRecovery.tableAt (CodeMap.registry _ (right.state rightLength)) (q.toFun name) key) at known
  rwa [NominalConfluence.tableAt_registry, NominalConfluence.tableAt_registry] at known

end Cordis.Repairs.NominalOpenConfluence

namespace Cordis.Repairs.NominalOpenConfluence
open Calculus Stages LegalHistory GuardedHistory
open PaperEffectEquations (CoeffectOperations)
open TypedRegistry (encodeProgram Scalar)
universe u
variable {Name Key Code : Type u} {V : Key → Type u} {ops : CoeffectOperations V}
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

/-- An endpoint agrees with its open reduction. -/
private theorem reduction_agrees (observe : ∀ key, Setoid (V key))
    {original pruned reduced : TypedRegistry.RawRegistry Name ops Code}
    (erased : GuardedHistory.VestigeErasures original pruned)
    (related : @StageSimulation.Related Name Key (Scalar ops) Code _ (TypedCoeffectReplay.setoid observe) Eq
      pruned reduced) :
    GuardedConfluence.EndpointAgreement observe original reduced := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  obtain ⟨p, compared⟩ := GuardedCutState.ProjectedAgreement.of_related related
  exact ⟨p, pruned, reduced, erased, .refl _, compared⟩

/-- The general case, histories with closed episodes as well as child
commands. As in `compare_surviving_endpoints`, the two quiet histories are
compared through open quiet reductions with the same surviving addressed
input. Freshness is asked of the surviving births: a reduction may rename
names, so it is stated for the reductions rather than the originals. -/
theorem nominal_confluence {program : Code → TypedRegistry.Instruction Name ops Code}
    (N : NominalConfluence.Nominal program) (observe : ∀ key, Setoid (V key))
    {left right leftPruned rightPruned : TypedRegistry.RawRegistry Name ops Code} {firstLength secondLength : Nat}
    (first : Trace (encodeProgram program) firstLength) (second : Trace (encodeProgram program) secondLength)
    (leftErased : GuardedHistory.VestigeErasures left leftPruned)
    (rightErased : GuardedHistory.VestigeErasures right rightPruned)
    (leftRelated : @StageSimulation.Related Name Key (Scalar ops) Code _ (TypedCoeffectReplay.setoid observe) Eq
      leftPruned (first.state firstLength))
    (rightRelated : @StageSimulation.Related Name Key (Scalar ops) Code _ (TypedCoeffectReplay.setoid observe) Eq
      rightPruned (second.state secondLength))
    (firstFresh : NominalConfluence.DrawsFresh N first) (secondFresh : NominalConfluence.DrawsFresh N second)
    (firstOpen : ¬ Nonempty (ClosedEpisode first)) (secondOpen : ¬ Nonempty (ClosedEpisode second))
    (firstQuiet : Progress.Quiet (first.state firstLength)) (secondQuiet : Progress.Quiet (second.state secondLength))
    (input : GuardedBirthAddresses.orchestrationInput first = GuardedBirthAddresses.orchestrationInput second)
    (contracts : GuardedCanonicalSchedule.OperationContracts ops observe) :
    ∃ p : Renaming.Permutation Name, ∀ name key, Iterators.OptionRel (TypedCoeffectReplay.setoid observe).r
      (StageRecovery.tableAt left name key) (StageRecovery.tableAt right (p.toFun name) key) := by
  obtain ⟨a, toFirst⟩ := (reduction_agrees observe leftErased leftRelated).tables observe
  obtain ⟨q, across⟩ := nominal_open_confluence N first second firstFresh secondFresh firstOpen secondOpen
    firstQuiet secondQuiet input observe contracts
  obtain ⟨b, fromSecond⟩ := ((reduction_agrees observe rightErased rightRelated).symm observe).tables observe
  have transitive : ∀ x y z : Scalar ops, (TypedCoeffectReplay.setoid observe).r x y →
      (TypedCoeffectReplay.setoid observe).r y z → (TypedCoeffectReplay.setoid observe).r x z :=
    fun _ _ _ => (TypedCoeffectReplay.setoid observe).trans
  refine ⟨a.trans (q.trans b), fun name key => ?_⟩
  exact Iterators.OptionRel.trans transitive (toFirst name key)
    (Iterators.OptionRel.trans transitive (across (a.toFun name) key) (fromSecond (q.toFun (a.toFun name)) key))

end Cordis.Repairs.NominalOpenConfluence

namespace Cordis.Repairs.NominalOpenConfluence
open Calculus Stages LegalHistory GuardedHistory
open PaperEffectEquations (CoeffectOperations)
open TypedRegistry (encodeProgram Scalar)
universe u
variable {Name Key Code : Type u} {V : Key → Type u} {ops : CoeffectOperations V}
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

/-! ## Reducing in the quotient

Excision is run on the image of a history in the quotient program, where
`ChildContinuations` holds and no freshness is needed. Only the original
history's draws must be fresh, to form its image. -/

/-- Every quiet history with fresh draws has an open quiet reduction of
its image in the quotient program. -/
theorem image_reduction {program : Code → TypedRegistry.Instruction Name ops Code}
    (N : NominalConfluence.Nominal program) {last : Nat} (trace : Trace (encodeProgram program) last)
    (fresh : NominalConfluence.DrawsFresh N trace) (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (contracts : GuardedCanonicalSchedule.OperationContracts ops observe) :
    ∃ (length : Nat) (result : Trace (encodeProgram (NominalConfluence.quotient N)) length)
      (projected : TypedRegistry.RawRegistry Name ops (NominalConfluence.Orbit N)),
      ¬ Nonempty (ClosedEpisode result) ∧ Progress.Quiet (result.state length) ∧
      GuardedHistory.VestigeErasures (CodeMap.registry (NominalConfluence.quot N) (trace.state last)) projected ∧
      @StageSimulation.Related Name Key (Scalar ops) (NominalConfluence.Orbit N) _
        (TypedCoeffectReplay.setoid observe) Eq projected (result.state length) := by
  obtain ⟨length, result, _, _, isOpen, _, _, _, settled, _, projected, erased, related⟩ :=
    GuardedHistory.eliminate_closed_episodes
      (CodeMap.mapTrace (NominalConfluence.compatible N) trace (NominalConfluence.draws_agree N fresh))
      (NominalConfluence.quiet_registry quiet) observe contracts.recovery contracts.commutative contracts.respect
  exact ⟨length, result, projected, isOpen, settled, erased, related⟩

/-- The general case with freshness asked only of the original histories.
Two quiet histories are compared through open quiet reductions of their
images in the quotient program, which `image_reduction` supplies, with
the same surviving addressed input. Their endpoint tables agree up to a
renaming. -/
theorem nominal_confluence_of_images {program : Code → TypedRegistry.Instruction Name ops Code}
    (N : NominalConfluence.Nominal program) (observe : ∀ key, Setoid (V key))
    {left right : TypedRegistry.RawRegistry Name ops Code}
    {leftPruned rightPruned : TypedRegistry.RawRegistry Name ops (NominalConfluence.Orbit N)}
    {firstLength secondLength : Nat}
    (first : Trace (encodeProgram (NominalConfluence.quotient N)) firstLength)
    (second : Trace (encodeProgram (NominalConfluence.quotient N)) secondLength)
    (leftErased : GuardedHistory.VestigeErasures (CodeMap.registry (NominalConfluence.quot N) left) leftPruned)
    (rightErased : GuardedHistory.VestigeErasures (CodeMap.registry (NominalConfluence.quot N) right) rightPruned)
    (leftRelated : @StageSimulation.Related Name Key (Scalar ops) (NominalConfluence.Orbit N) _
      (TypedCoeffectReplay.setoid observe) Eq leftPruned (first.state firstLength))
    (rightRelated : @StageSimulation.Related Name Key (Scalar ops) (NominalConfluence.Orbit N) _
      (TypedCoeffectReplay.setoid observe) Eq rightPruned (second.state secondLength))
    (firstOpen : ¬ Nonempty (ClosedEpisode first)) (secondOpen : ¬ Nonempty (ClosedEpisode second))
    (firstQuiet : Progress.Quiet (first.state firstLength)) (secondQuiet : Progress.Quiet (second.state secondLength))
    (input : GuardedBirthAddresses.orchestrationInput first = GuardedBirthAddresses.orchestrationInput second)
    (contracts : GuardedCanonicalSchedule.OperationContracts ops observe) :
    ∃ p : Renaming.Permutation Name, ∀ name key, Iterators.OptionRel (TypedCoeffectReplay.setoid observe).r
      (StageRecovery.tableAt left name key) (StageRecovery.tableAt right (p.toFun name) key) := by
  obtain ⟨agreement, _⟩ := GuardedConfluence.compare_surviving_endpoints observe first second
    leftErased rightErased leftRelated rightRelated (NominalConfluence.quotient_child_continuations N)
    firstOpen secondOpen firstQuiet secondQuiet input contracts.recovery contracts.commutative contracts.respect
  obtain ⟨p, tables⟩ := agreement.tables observe
  refine ⟨p, fun name key => ?_⟩
  have known := tables name key
  rwa [NominalConfluence.tableAt_registry, NominalConfluence.tableAt_registry] at known

end Cordis.Repairs.NominalOpenConfluence
