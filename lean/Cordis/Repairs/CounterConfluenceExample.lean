import Cordis.Repairs.CounterContracts
import Cordis.Repairs.GuardedNameExtension

/-! The endpoint comparison of the repaired Theorem 80, applied to two
histories whose consumer really operates. A provider installs 7 in an
integer counter, a consumer adds 1 to it, and an independent root runs
either before or after both. The three operation contracts are discharged
by `CounterContracts`, not vacuously by an empty operation family.
The histories follow `StagePriorityExample`, with its consumer given a
real operation. -/
namespace Cordis.Repairs.CounterConfluenceExample
open Calculus Stages LegalHistory GuardedHistory
open Vestigial (cutNotes eventActor)

abbrev Name := Fin 3
abbrev ops := CounterContracts.ops

inductive Code where
  | idle
  | supply
  | bump
  deriving DecidableEq

abbrev R := TypedRegistry.RawRegistry Name ops Code
abbrev F := TypedRegistry.RawFiber Name ops Code
abbrev Ev := Event Name Unit Code
abbrev I := Inverse Name Unit (TypedRegistry.Scalar ops)

def codeOf (name : Name) : Code :=
  if name = 0 then .bump else if name = 2 then .supply else .idle

def component (name : Name) : Component Unit Code :=
  ⟨fun _ => name == 0, fun _ => name == 2, codeOf name⟩

def entry : Code → TypedRegistry.Instruction Name ops Code
  | .idle => ⟨.unit, fun _ => none⟩
  | .supply => ⟨.provide () (7 : Int), fun _ => none⟩
  | .bump => ⟨.operate () PUnit.unit (1 : Int), fun _ => none⟩

abbrev program := TypedRegistry.encodeProgram entry

def view : View Name Unit := fun _ => 2
def value : TypedRegistry.Scalar ops := TypedCoeffectReplay.pack () (7 : Int)
def bumped : TypedRegistry.Scalar ops := TypedCoeffectReplay.pack () (8 : Int)
def undo : TypedRegistry.Scalar ops → TypedRegistry.Scalar ops :=
  TypedCoeffectReplay.encodeMap () (fun w : Int => some (w - 1))

def loading (name : Name) : Phase Name Unit Code I :=
  .reloading (component name).entry [] view

def active (name : Name) : Phase Name Unit Code I :=
  .active (if name = 2 then [.restrict 2 ()] else if name = 0 then [.operate 2 () undo] else [.unit]) view

def events (early : Bool) : Nat → Ev
  | 0 => .command (.insert 0 (component 0))
  | 1 => .command (.insert 1 (component 1))
  | 2 => .command (.insert 2 (component 2))
  | 3 => .lifecycle .begin (if early then 1 else 2)
  | 4 => if early then .lifecycle .begin 2 else .lifecycle .finish 2
  | 5 => if early then .lifecycle .finish 2 else .lifecycle .begin 0
  | 6 => if early then .lifecycle .begin 0 else .lifecycle .finish 0
  | 7 => if early then .lifecycle .finish 0 else .lifecycle .begin 1
  | _ => .lifecycle .finish 1

private def applyEvent (source : R) : Ev → R
  | .command command => command.apply source
  | .lifecycle .begin name => mark source name (loading name)
  | .lifecycle .finish name =>
    mark (if name = 2 then write source 2 () (some value)
      else if name = 0 then write source 2 () (some bumped) else source) name (active name)
  | _ => source

def states (early : Bool) : Nat → R
  | 0 => fun _ => none
  | cut + 1 => applyEvent (states early cut) (events early cut)

private theorem names (name : Name) : name = 0 ∨ name = 1 ∨ name = 2 := by
  have within := name.isLt
  have values : name.val = 0 ∨ name.val = 1 ∨ name.val = 2 := by omega
  rcases values with first | second | third
  · exact .inl (Fin.ext first)
  · exact .inr (.inl (Fin.ext second))
  · exact .inr (.inr (Fin.ext third))

private theorem no_parent (name : Name) : (none : Option Name) = some name → False := Option.noConfusion

private theorem first_insertion (early : Bool) : Insertable (states early 0) 0 (component 0) none :=
  ⟨rfl, fun name absent => False.elim (no_parent name absent), fun _ _ => trivial⟩

private theorem second_insertion (early : Bool) : Insertable (states early 1) 1 (component 1) none := by
  refine ⟨rfl, fun name absent => False.elim (no_parent name absent), ?_⟩
  intro name key
  rcases names name with rfl | rfl | rfl
  · exact fun impossible => Bool.noConfusion impossible
  · trivial
  · trivial

private theorem third_insertion (early : Bool) : Insertable (states early 2) 2 (component 2) none := by
  refine ⟨rfl, fun name absent => False.elim (no_parent name absent), ?_⟩
  intro name key
  rcases names name with rfl | rfl | rfl
  · exact fun _ impossible => Bool.noConfusion impossible
  · exact fun _ impossible => Bool.noConfusion impossible
  · trivial

private theorem independent_target {r : R} {name : Name} {row : F}
    (found : r name = some row) (unretired : row.retired = false)
    (requires : row.component.requires () = false) : Target r name view := by
  rw [Target, found]
  refine ⟨unretired, ?_⟩
  intro key needed
  cases key
  exact False.elim (Bool.noConfusion (requires.symm.trans needed))

private theorem consumer_target {r : R} {row provider : F}
    (found : r 0 = some row) (unretired : row.retired = false) (source : r 2 = some provider)
    (available : provider.phase.available) (bound : provider.table () ≠ none) : Target r 0 view := by
  rw [Target, found]
  refine ⟨unretired, ?_⟩
  intro key _
  cases key
  simpa only [view, source] using And.intro available bound

private theorem start_step {early : Bool} {cut : Nat} {name : Name} {row : F}
    (event : events early cut = .lifecycle .begin name)
    (found : states early cut name = some row) (inactive : row.phase = .inactive)
    (entryCode : row.component.entry = (component name).entry) (target : Target (states early cut) name view) :
    GuardedSuffix.Transition program (cutNotes (states early) (fun i => eventActor (events early i)) cut)
      (events early cut) (states early cut) (states early (cut + 1)) := by
  have endpoint : states early (cut + 1) = mark (states early cut) name (loading name) := by
    rw [states, event]
    rfl
  rw [event, endpoint]
  change Labeled.Step program .begin name (states early cut) _
  unfold loading
  rw [← entryCode]
  exact .begin _ _ _ view found inactive (by unfold ErrorFree; rw [found]; exact Option.noConfusion) target

private theorem finish_idle {early : Bool} {cut : Nat} {row : F}
    (event : events early cut = .lifecycle .finish 1)
    (found : states early cut 1 = some row) (reloading : row.phase = .reloading .idle [] view)
    (target : Target (states early cut) 1 view) :
    GuardedSuffix.Transition program (cutNotes (states early) (fun i => eventActor (events early i)) cut)
      (events early cut) (states early cut) (states early (cut + 1)) := by
  have endpoint : states early (cut + 1) = mark (states early cut) 1 (.active [.unit] view) := by
    rw [states, event]
    simp [applyEvent, active]
  rw [event, endpoint]
  exact Labeled.Step.finish _ _ _ row .idle [] view .unit found reloading target (.unit _ _ _ rfl)

private theorem finish_provider {early : Bool} {cut : Nat} {row : F}
    (event : events early cut = .lifecycle .finish 2)
    (found : states early cut 2 = some row) (reloading : row.phase = .reloading .supply [] view)
    (declared : row.component.provides () = true) (vacant : row.table () = none)
    (target : Target (states early cut) 2 view) :
    GuardedSuffix.Transition program (cutNotes (states early) (fun i => eventActor (events early i)) cut)
      (events early cut) (states early cut) (states early (cut + 1)) := by
  have endpoint : states early (cut + 1) =
      mark (write (states early cut) 2 () (some value)) 2 (.active [.restrict 2 ()] view) := by
    rw [states, event]
    rfl
  rw [event, endpoint]
  exact Labeled.Step.finish _ _ _ row .supply [] view (.restrict 2 ()) found reloading target
    (.provide _ _ _ row () value rfl found declared vacant)

/-- The consumer's operation reads the provider's 7 and writes 8 back. -/
private theorem finish_consumer {early : Bool} {cut : Nat} {row : F}
    (event : events early cut = .lifecycle .finish 0)
    (found : states early cut 0 = some row) (reloading : row.phase = .reloading .bump [] view)
    (located : location (states early cut) 0 () = some (2, value))
    (target : Target (states early cut) 0 view) :
    GuardedSuffix.Transition program (cutNotes (states early) (fun i => eventActor (events early i)) cut)
      (events early cut) (states early cut) (states early (cut + 1)) := by
  have endpoint : states early (cut + 1) =
      mark (write (states early cut) 2 () (some bumped)) 0 (.active [.operate 2 () undo] view) := by
    rw [states, event]
    rfl
  rw [event, endpoint]
  have landed : Land program 0 .bump (states early cut) (write (states early cut) 2 () (some bumped))
      (.operate 2 () undo) none :=
    Execution.operate (result := fun code => (program code).next) (states early cut) 0 .bump ()
      (TypedRegistry.encodeOperation ops () PUnit.unit (1 : Int)) 2 value bumped undo
      (TypedRegistry.packOutcome ops () PUnit.unit PUnit.unit) rfl located rfl
  exact Labeled.Step.finish _ _ _ row .bump [] view (.operate 2 () undo) found reloading target landed

def trace (early : Bool) : Trace program 9 where
  state := states early
  notes := cutNotes (states early) (fun cut => eventActor (events early cut))
  event := events early
  start := rfl
  seed := rfl
  step cut bounded := by
    refine ⟨?_, rfl⟩
    have casesCut : cut = 0 ∨ cut = 1 ∨ cut = 2 ∨ cut = 3 ∨ cut = 4 ∨
        cut = 5 ∨ cut = 6 ∨ cut = 7 ∨ cut = 8 := by omega
    rcases casesCut with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨first_insertion early, rfl⟩
    · exact ⟨second_insertion early, rfl⟩
    · exact ⟨third_insertion early, rfl⟩
    all_goals cases early
    all_goals first
      | exact start_step rfl rfl rfl rfl (independent_target rfl rfl rfl)
      | exact finish_provider rfl rfl rfl rfl rfl (independent_target rfl rfl rfl)
      | exact start_step rfl rfl rfl rfl (consumer_target rfl rfl rfl trivial Option.noConfusion)
      | exact finish_consumer rfl rfl rfl rfl (consumer_target rfl rfl rfl trivial Option.noConfusion)
      | exact finish_idle rfl rfl rfl (independent_target rfl rfl rfl)

theorem quiet (early : Bool) : Progress.Quiet ((trace early).state 9) := by
  intro name row found
  cases early <;> rcases names name with rfl | rfl | rfl
  all_goals
    change some _ = some row at found
    cases Option.some.inj found
    first
    | exact consumer_target rfl rfl rfl trivial Option.noConfusion
    | exact independent_target rfl rfl rfl

theorem open_only (early : Bool) : ¬ Nonempty (ClosedEpisode (trace early)) := by
  rintro ⟨episode⟩
  obtain ⟨unload, _⟩ := unload_boundary (trace early) episode.interval
  have bound := episode.interval.bounded
  have cuts : episode.closed = 0 ∨ episode.closed = 1 ∨ episode.closed = 2 ∨ episode.closed = 3 ∨
      episode.closed = 4 ∨ episode.closed = 5 ∨ episode.closed = 6 ∨ episode.closed = 7 ∨ episode.closed = 8 := by omega
  change events early episode.closed = .lifecycle .unload episode.name at unload
  cases early <;> rcases cuts with cut | cut | cut | cut | cut | cut | cut | cut | cut <;>
    simp [cut, events] at unload

/-- The operation ran in both histories: the provider ends holding 8. -/
theorem counter_bumped (early : Bool) :
    ((trace early).state 9 2).bind (fun row => row.table ()) = some bumped := by
  cases early <;> rfl

theorem stable : GuardedLandingMatching.ChildContinuations program := by
  intro code _ _ _ _
  cases code <;> rfl

/-- The repaired endpoint comparison, with all three operation contracts
supplied by a real operation family. -/
theorem counter_confluence :
    letI : Setoid (TypedRegistry.Scalar ops) := TypedCoeffectReplay.setoid CounterContracts.observe
    GuardedCutState.ProjectedAgreement ((trace true).state 9) ((trace false).state 9) :=
  (GuardedNameExtension.compare_open_endpoints (trace true) (trace false)
    (open_only true) (quiet true) (open_only false) (quiet false) stable rfl CounterContracts.observe
    CounterContracts.recovery (fun _ => CounterContracts.commutative)
    (fun _ => CounterContracts.respect)).2.1

/-- No external command targets a child: there are no retirements or removals. -/
theorem roots_only (early : Bool) :
    GuardedCanonicalSchedule.RootOnlyInput (GuardedBirthAddresses.orchestrationInput (trace early)) := by
  rw [GuardedCanonicalSchedule.root_only_input_iff_root_targets]
  intro cut bounded name command
  exfalso
  have cuts : cut = 0 ∨ cut = 1 ∨ cut = 2 ∨ cut = 3 ∨ cut = 4 ∨
      cut = 5 ∨ cut = 6 ∨ cut = 7 ∨ cut = 8 := by omega
  change events early cut = _ ∨ events early cut = _ at command
  cases early <;> rcases cuts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [events] at command

/-- The headline root-only case of the repaired Theorem 80(2), applied to
two quiet histories with equal root commands and a real operation. -/
theorem counter_endpoint_agreement :
    GuardedConfluence.EndpointAgreement CounterContracts.observe ((trace true).state 9) ((trace false).state 9) :=
  GuardedCanonicalSchedule.confluence_of_root_only_input (trace true) (trace false) (quiet true) (quiet false)
    (roots_only true) (roots_only false) rfl stable CounterContracts.observe
    CounterContracts.recovery (fun _ => CounterContracts.commutative) (fun _ => CounterContracts.respect)

end Cordis.Repairs.CounterConfluenceExample
