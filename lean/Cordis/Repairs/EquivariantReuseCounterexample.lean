import Cordis.Repairs.GuardedCanonicalSchedule
import Cordis.Repairs.GuardedEpisodeExample

/-! Weakening `ChildContinuations` to renaming equivariance does not save
Theorem 80. Here codes may carry names, and the parent's program commutes
with every renaming of names. It stores its first child's name and, at
its second birth, compares the drawn name with the stored one. After the
first child is retired and removed, the second draw may reuse its name or
take a fresh one. The two histories have identical events, commands, and
surviving input, and both are quiet and open, but the parent publishes 1
in one and 2 in the other, so their endpoints do not agree.
It builds on the repository's `PinnedRedrawExample`, which already forces a
second birth to reuse a removed child's name, and on the draw-dependence
counterexamples for Lemmas 57 and 66. -/
namespace Cordis.Repairs.EquivariantReuseCounterexample
open Calculus Stages LegalHistory GuardedHistory
open Vestigial (cutNotes eventActor)
open GuardedEpisodeExample (operations observe)

abbrev Name := Fin 3

inductive Code where
  | start
  | waiting (first : Name)
  | same
  | different
  | idle
  deriving DecidableEq

abbrev R := TypedRegistry.RawRegistry Name operations Code
abbrev F := TypedRegistry.RawFiber Name operations Code
abbrev Ev := Event Name Unit Code

def parent : Component Unit Code := ⟨fun _ => false, fun _ => true, .start⟩
def child : Component Unit Code := ⟨fun _ => false, fun _ => false, .idle⟩

def entry : Code → TypedRegistry.Instruction Name operations Code
  | .start => ⟨.instantiate child, fun
      | .child first => some (.waiting first)
      | _ => none⟩
  | .waiting first => ⟨.instantiate child, fun
      | .child second => some (if second = first then .same else .different)
      | _ => none⟩
  | .same => ⟨.provide () 1, fun _ => none⟩
  | .different => ⟨.provide () 2, fun _ => none⟩
  | .idle => ⟨.unit, fun _ => none⟩

abbrev program := TypedRegistry.encodeProgram entry

/-! ## Renaming equivariance -/

/-- The name action on codes: only a stored first child moves. -/
def act (χ : Renaming.Permutation Name) : Code → Code
  | .waiting first => .waiting (χ.toFun first)
  | code => code

def renameAction (χ : Renaming.Permutation Name) :
    TypedRegistry.Action Name operations Code → TypedRegistry.Action Name operations Code
  | .unit => .unit
  | .provide key value => .provide key value
  | .operate key name argument => .operate key name argument
  | .instantiate component => .instantiate { component with entry := act χ component.entry }

def renameOutcome (χ : Renaming.Permutation Name) :
    TypedRegistry.Outcome Name operations → TypedRegistry.Outcome Name operations
  | .unit => .unit
  | .provision key value => .provision key value
  | .operation key name outcome => .operation key name outcome
  | .child name => .child (χ.toFun name)

/-- A program commutes with renaming when renaming a code renames its
action, and renaming an outcome renames the selected continuation. -/
def Equivariant (program : Code → TypedRegistry.Instruction Name operations Code) : Prop :=
  ∀ χ code, (program (act χ code)).action = renameAction χ (program code).action ∧
    ∀ outcome, (program (act χ code)).next (renameOutcome χ outcome) =
      ((program code).next outcome).map (act χ)

theorem act_identity (code : Code) : act Renaming.Permutation.identity code = code := by
  cases code <;> rfl

theorem act_trans (first second : Renaming.Permutation Name) (code : Code) :
    act second (act first code) = act (first.trans second) code := by
  cases code <;> rfl

theorem equivariant : Equivariant entry := by
  intro χ code
  cases code with
  | start =>
    refine ⟨rfl, ?_⟩
    intro outcome
    cases outcome <;> rfl
  | waiting first =>
    refine ⟨rfl, ?_⟩
    intro outcome
    cases outcome with
    | child second =>
      simp only [entry, renameOutcome, act, Renaming.Permutation.eq_iff, Option.map_some]
      by_cases same : second = first <;> simp [same]
    | _ => rfl
  | same => exact ⟨rfl, fun outcome => by cases outcome <;> rfl⟩
  | different => exact ⟨rfl, fun outcome => by cases outcome <;> rfl⟩
  | idle => exact ⟨rfl, fun outcome => by cases outcome <;> rfl⟩

/-- The program is outside the scope of the repaired Theorem 80. -/
theorem not_child_continuations : ¬ GuardedLandingMatching.ChildContinuations program := by
  intro stable
  have selected := stable (.waiting 1) child rfl 1 2
  change some Code.same = some Code.different at selected
  cases selected

/-! ## Two histories differing only in the second draw -/

def view : View Name Unit := fun _ => 0
def value (reuse : Bool) : TypedRegistry.Scalar operations :=
  TypedCoeffectReplay.pack () (if reuse then 1 else 2)
def second (reuse : Bool) : Name := if reuse then 1 else 2
def verdict (reuse : Bool) : Code := if reuse then .same else .different

def empty : R := fun _ => none
def s1 : R := put empty 0 (fresh parent none)
def s2 : R := mark s1 0 (.reloading .start [] view)
def s3 : R := mark (put s2 1 (fresh child (some 0))) 0 (.reloading (.waiting 1) [.retire 1] view)
def s4 : R := retire s3 1
def s5 : R := erase s4 1
def s6 (reuse : Bool) : R :=
  mark (put s5 (second reuse) (fresh child (some 0))) 0
    (.reloading (verdict reuse) [.retire (second reuse), .retire 1] view)
def s7 (reuse : Bool) : R :=
  mark (write (s6 reuse) 0 () (some (value reuse))) 0
    (.active [.restrict 0 (), .retire (second reuse), .retire 1] view)
def s8 (reuse : Bool) : R := retire (s7 reuse) (second reuse)

def states (reuse : Bool) : Nat → R
  | 0 => empty | 1 => s1 | 2 => s2 | 3 => s3 | 4 => s4 | 5 => s5
  | 6 => s6 reuse | 7 => s7 reuse | _ => s8 reuse

def events (reuse : Bool) : Nat → Ev
  | 0 => .command (.insert 0 parent)
  | 1 => .lifecycle .begin 0
  | 2 => .lifecycle .iter 0
  | 3 => .command (.retire 1)
  | 4 => .command (.remove 1)
  | 5 => .lifecycle .iter 0
  | 6 => .lifecycle .finish 0
  | _ => .command (.retire (second reuse))

private theorem name_cases (name : Name) : name = 0 ∨ name = 1 ∨ name = 2 := by
  have within := name.isLt
  have values : name.val = 0 ∨ name.val = 1 ∨ name.val = 2 := by omega
  rcases values with first | second | third
  · exact .inl (Fin.ext first)
  · exact .inr (.inl (Fin.ext second))
  · exact .inr (.inr (Fin.ext third))

private theorem firstBirth : Insertable s2 1 child (some 0) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro name equal
    cases equal
    change some _ ≠ none
    simp
  · intro name key
    rcases name_cases name with rfl | rfl | rfl
    · exact fun impossible => Bool.noConfusion impossible
    · trivial
    · trivial

private theorem release : Removable s4 1 := by
  refine ⟨rfl, rfl, fun _ => rfl, ?_⟩
  intro name
  rcases name_cases name with rfl | rfl | rfl
  · change (none : Option Name) ≠ some 1; simp
  · change (some 0 : Option Name) ≠ some 1; decide
  · trivial

private theorem secondBirth (reuse : Bool) : Insertable s5 (second reuse) child (some 0) := by
  refine ⟨by cases reuse <;> rfl, ?_, ?_⟩
  · intro name equal
    cases equal
    change some _ ≠ none
    simp
  · intro name key
    rcases name_cases name with rfl | rfl | rfl
    · exact fun impossible => Bool.noConfusion impossible
    · trivial
    · trivial

def trace (reuse : Bool) : Trace program 8 where
  state := states reuse
  notes := cutNotes (states reuse) (fun cut => eventActor (events reuse cut))
  event := events reuse
  start := rfl
  seed := rfl
  step cut valid := by
    have cuts : cut = 0 ∨ cut = 1 ∨ cut = 2 ∨ cut = 3 ∨ cut = 4 ∨ cut = 5 ∨ cut = 6 ∨ cut = 7 := by omega
    rcases cuts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨⟨rfl, by simp, fun _ _ => trivial⟩, rfl⟩, rfl⟩
    · exact ⟨.begin s1 0 (fresh parent none) view rfl rfl (by change some _ ≠ none; simp)
        ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩, rfl⟩
    · exact ⟨.iter s2 _ 0 { (fresh parent none : F) with phase := .reloading .start [] view }
        .start [] view (.retire 1) (.waiting 1) rfl rfl ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
        (.instantiate s2 0 .start child 1 rfl firstBirth), rfl⟩
    · exact ⟨⟨by change some _ ≠ none; simp, rfl⟩, rfl⟩
    · exact ⟨⟨release, rfl⟩, rfl⟩
    · cases reuse
      · exact ⟨.iter s5 _ 0 { (fresh parent none : F) with phase := .reloading (.waiting 1) [.retire 1] view }
          (.waiting 1) [.retire 1] view (.retire 2) .different rfl rfl
          ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
          (.instantiate s5 0 (.waiting 1) child 2 rfl (secondBirth false)), rfl⟩
      · exact ⟨.iter s5 _ 0 { (fresh parent none : F) with phase := .reloading (.waiting 1) [.retire 1] view }
          (.waiting 1) [.retire 1] view (.retire 1) .same rfl rfl
          ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
          (.instantiate s5 0 (.waiting 1) child 1 rfl (secondBirth true)), rfl⟩
    · cases reuse
      · exact ⟨.finish (s6 false) _ 0
          { (fresh parent none : F) with phase := .reloading .different [.retire 2, .retire 1] view }
          .different [.retire 2, .retire 1] view (.restrict 0 ()) rfl rfl
          ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
          (.provide _ _ _ { (fresh parent none : F) with phase := .reloading .different [.retire 2, .retire 1] view }
            () (value false) rfl rfl rfl rfl), rfl⟩
      · exact ⟨.finish (s6 true) _ 0
          { (fresh parent none : F) with phase := .reloading .same [.retire 1, .retire 1] view }
          .same [.retire 1, .retire 1] view (.restrict 0 ()) rfl rfl
          ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
          (.provide _ _ _ { (fresh parent none : F) with phase := .reloading .same [.retire 1, .retire 1] view }
            () (value true) rfl rfl rfl rfl), rfl⟩
    · cases reuse <;> exact ⟨⟨by change some _ ≠ none; simp, rfl⟩, rfl⟩

theorem open_only (reuse : Bool) : ¬ Nonempty (ClosedEpisode (trace reuse)) := by
  rintro ⟨closed⟩
  obtain ⟨unload, _⟩ := unload_boundary (trace reuse) closed.interval
  change events reuse closed.closed = .lifecycle .unload closed.name at unload
  have bound := closed.interval.bounded
  have cuts : closed.closed = 0 ∨ closed.closed = 1 ∨ closed.closed = 2 ∨ closed.closed = 3 ∨
      closed.closed = 4 ∨ closed.closed = 5 ∨ closed.closed = 6 ∨ closed.closed = 7 := by omega
  rcases cuts with cut | cut | cut | cut | cut | cut | cut | cut <;> simp [events, cut] at unload

def parentEnd (reuse : Bool) : F :=
  { (fresh parent none : F) with
    table := fun other => if other = () then some (value reuse) else none
    phase := .active [.restrict 0 (), .retire (second reuse), .retire 1] view }

def childEnd : F := { (fresh child (some 0) : F) with retired := true }

theorem quiet (reuse : Bool) : Progress.Quiet ((trace reuse).state 8) := by
  intro name row found
  cases reuse <;> rcases name_cases name with rfl | rfl | rfl
  · have known : (trace false).state 8 0 = some (parentEnd false) := rfl
    rw [known] at found
    cases Option.some.inj found
    exact ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
  · exact absurd found (by change (none : Option F) ≠ _; simp)
  · have known : (trace false).state 8 2 = some childEnd := rfl
    rw [known] at found
    cases Option.some.inj found
    intro _ target
    exact Bool.noConfusion target.1
  · have known : (trace true).state 8 0 = some (parentEnd true) := rfl
    rw [known] at found
    cases Option.some.inj found
    exact ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
  · have known : (trace true).state 8 1 = some childEnd := rfl
    rw [known] at found
    cases Option.some.inj found
    intro _ target
    exact Bool.noConfusion target.1
  · exact absurd found (by change (none : Option F) ≠ _; simp)

/-! ## The surviving input is the same -/

open GuardedBirthAddresses (Addressed AddressedCommand Address occurrencesBefore commandAt targetAt)

def firstAddress : Address := .child (.root 0) 0
def secondAddress : Address := .child (.root 0) 1

private theorem root_address (reuse : Bool) : Addressed (trace reuse) 1 (.root 0) :=
  Addressed.root (time := 0) (name := 0) (component := parent) (by decide) rfl

private theorem first_address (reuse : Bool) : Addressed (trace reuse) 3 firstAddress := by
  have born := Addressed.child (trace := trace reuse) (time := 2) (parentBirth := 1) (name := 1)
    (by decide) rfl rfl (by cases reuse <;> exact Option.noConfusion) (by cases reuse <;> rfl) (root_address reuse)
  have ordinal : occurrencesBefore (GuardedBirthAddresses.isParentStage (trace reuse) 1) 2 = 0 := by
    cases reuse <;> rfl
  rw [ordinal] at born
  exact born

private theorem second_address (reuse : Bool) : Addressed (trace reuse) 6 secondAddress := by
  have born := Addressed.child (trace := trace reuse) (time := 5) (parentBirth := 1) (name := second reuse)
    (by decide) rfl (by cases reuse <;> rfl) (by cases reuse <;> exact Option.noConfusion)
    (by cases reuse <;> rfl) (root_address reuse)
  have ordinal : occurrencesBefore (GuardedBirthAddresses.isParentStage (trace reuse) 1) 5 = 1 := by
    cases reuse <;> rfl
  rw [ordinal] at born
  exact born

private theorem command3 (reuse : Bool) :
    commandAt (trace reuse) 3 = some (.retire firstAddress child) := by
  have target : targetAt (trace reuse) 3 1 = some (firstAddress, child) :=
    (GuardedBirthAddresses.targetAt_eq_some _).mpr
      ⟨3, fresh child (some 0), by cases reuse <;> rfl, first_address reuse, by cases reuse <;> rfl, rfl⟩
  have event : (trace reuse).event 3 = .command (.retire 1) := rfl
  simp only [commandAt, event, target, Option.map_some]

private theorem command4 (reuse : Bool) :
    commandAt (trace reuse) 4 = some (.remove firstAddress child) := by
  have target : targetAt (trace reuse) 4 1 = some (firstAddress, child) :=
    (GuardedBirthAddresses.targetAt_eq_some _).mpr
      ⟨3, childEnd, by cases reuse <;> rfl, first_address reuse, by cases reuse <;> rfl, rfl⟩
  have event : (trace reuse).event 4 = .command (.remove 1) := rfl
  simp only [commandAt, event, target, Option.map_some]

private theorem command7 (reuse : Bool) :
    commandAt (trace reuse) 7 = some (.retire secondAddress child) := by
  have target : targetAt (trace reuse) 7 (second reuse) = some (secondAddress, child) :=
    (GuardedBirthAddresses.targetAt_eq_some _).mpr
      ⟨6, fresh child (some 0), by cases reuse <;> rfl, second_address reuse, by cases reuse <;> rfl, rfl⟩
  have event : (trace reuse).event 7 = .command (.retire (second reuse)) := rfl
  simp only [commandAt, event, target, Option.map_some]

theorem input (reuse : Bool) :
    GuardedBirthAddresses.orchestrationInput (trace reuse) =
      [.insert 0 parent, .retire firstAddress child, .remove firstAddress child,
        .retire secondAddress child] := by
  unfold GuardedBirthAddresses.orchestrationInput
  rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  have c0 : commandAt (trace reuse) 0 = some (.insert 0 parent) := rfl
  have c1 : commandAt (trace reuse) 1 = none := rfl
  have c2 : commandAt (trace reuse) 2 = none := rfl
  have c5 : commandAt (trace reuse) 5 = none := rfl
  have c6 : commandAt (trace reuse) 6 = none := rfl
  simp only [List.filterMap_cons, List.filterMap_nil, c0, c1, c2, command3, command4, c5, c6, command7]

/-- The commands, addressed by birth, are the same in both histories. -/
theorem same_input :
    GuardedBirthAddresses.orchestrationInput (trace true) =
      GuardedBirthAddresses.orchestrationInput (trace false) := by
  rw [input, input]

/-! ## The endpoints disagree -/

theorem published (reuse : Bool) :
    StageRecovery.tableAt ((trace reuse).state 8) 0 () = some (value reuse) := by
  cases reuse <;> rfl

theorem endpoints_disagree :
    ¬ GuardedConfluence.EndpointAgreement observe ((trace true).state 8) ((trace false).state 8) := by
  intro agrees
  obtain ⟨names, matched⟩ := agrees.tables observe
  have atParent := matched 0 ()
  rw [published true] at atParent
  rcases name_cases (names.toFun 0) with image | image | image <;> rw [image] at atParent
  · rw [published false] at atParent
    obtain ⟨same, distinct⟩ := atParent
    cases same
    change (if true = true then 1 else 2 : Nat) = (if false = true then 1 else 2) at distinct
    simp at distinct
  · exact atParent
  · exact atParent

theorem contracts : GuardedCanonicalSchedule.OperationContracts operations observe where
  recovery := fun _ action => nomatch action
  commutative := fun _ action => nomatch action
  respect := fun _ action => nomatch action

/-- Everything the repaired Theorem 80 asks of two histories holds here
except `ChildContinuations`, which is replaced by renaming equivariance,
and yet the endpoints disagree. -/
theorem equivariant_confluence_fails :
    Equivariant entry ∧ ¬ GuardedLandingMatching.ChildContinuations program ∧
      (∀ reuse, ¬ Nonempty (ClosedEpisode (trace reuse))) ∧
      (∀ reuse, Progress.Quiet ((trace reuse).state 8)) ∧
      GuardedBirthAddresses.orchestrationInput (trace true) =
        GuardedBirthAddresses.orchestrationInput (trace false) ∧
      GuardedCanonicalSchedule.OperationContracts operations observe ∧
      ¬ GuardedConfluence.EndpointAgreement observe ((trace true).state 8) ((trace false).state 8) :=
  ⟨equivariant, not_child_continuations, open_only, quiet, same_input, contracts, endpoints_disagree⟩

end Cordis.Repairs.EquivariantReuseCounterexample
