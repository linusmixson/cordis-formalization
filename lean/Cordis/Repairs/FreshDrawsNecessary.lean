import Cordis.Repairs.EquivariantReuseCounterexample
import Cordis.Repairs.NominalConfluence

/-! `DrawsFresh` cannot be dropped from `nominal_root_only_confluence`.
The program of `EquivariantReuseCounterexample` is nominal. Here a root
is inserted already holding the name 1 in its code, so no child commands
are needed. In one history its only birth draws the fresh name 2; in the
other it draws 1, which its code mentions. Every other hypothesis of the
theorem holds for both, and their endpoint tables do not agree up to any
renaming. -/
namespace Cordis.Repairs.FreshDrawsNecessary
open Calculus Stages LegalHistory GuardedHistory
open Vestigial (cutNotes eventActor)
open GuardedEpisodeExample (operations observe)
open EquivariantReuseCounterexample (Name Code R F entry program act child view value second verdict)

/-! ## The program is nominal -/

def supp : Code → Name → Prop
  | .waiting first, n => first = n
  | _, _ => False

def nominal : NominalConfluence.Nominal entry where
  act := act
  act_trans χ ψ c := by cases c <;> rfl
  act_symm χ c := by cases c <;> simp [act, Renaming.Permutation.symm]
  supp := supp
  fixes χ c fixed := by
    cases c with
    | waiting first => simp [act, fixed first rfl]
    | _ => rfl
  supp_act χ c n := by
    cases c <;> simp [act, supp]
  fresh c := by
    cases c with
    | waiting first =>
      by_cases zero : first = 0
      · exact ⟨1, by simp [supp, zero]⟩
      · exact ⟨0, by simpa [supp] using zero⟩
    | _ => exact ⟨0, id⟩
  action χ c := by cases c <;> rfl
  next χ c o := by
    cases c with
    | waiting first =>
      cases o with
      | child b =>
        simp only [entry, NominalConfluence.renameOutcome, act, Renaming.Permutation.eq_iff, Option.map_some]
        by_cases same : b = first <;> simp [same]
      | _ => rfl
    | _ => cases o <;> rfl

/-! ## Two root-only histories -/

def holder : Component Unit Code := ⟨fun _ => false, fun _ => true, .waiting 1⟩

def empty : R := fun _ => none
def s1 : R := put empty 0 (fresh holder none)
def s2 : R := mark s1 0 (.reloading (.waiting 1) [] view)
def s3 (reuse : Bool) : R :=
  mark (put s2 (second reuse) (fresh child (some 0))) 0
    (.reloading (verdict reuse) [.retire (second reuse)] view)
def s4 (reuse : Bool) : R :=
  mark (write (s3 reuse) 0 () (some (value reuse))) 0
    (.active [.restrict 0 (), .retire (second reuse)] view)
def s5 (reuse : Bool) : R := mark (s4 reuse) (second reuse) (.reloading .idle [] view)
def s6 (reuse : Bool) : R := mark (s5 reuse) (second reuse) (.active [.unit] view)

def states (reuse : Bool) : Nat → R
  | 0 => empty | 1 => s1 | 2 => s2 | 3 => s3 reuse | 4 => s4 reuse | 5 => s5 reuse | _ => s6 reuse

def events (reuse : Bool) : Nat → Event Name Unit Code
  | 0 => .command (.insert 0 holder)
  | 1 => .lifecycle .begin 0
  | 2 => .lifecycle .iter 0
  | 3 => .lifecycle .finish 0
  | 4 => .lifecycle .begin (second reuse)
  | _ => .lifecycle .finish (second reuse)

private theorem name_cases (name : Name) : name = 0 ∨ name = 1 ∨ name = 2 := by
  have within := name.isLt
  have values : name.val = 0 ∨ name.val = 1 ∨ name.val = 2 := by omega
  rcases values with first | second | third
  · exact .inl (Fin.ext first)
  · exact .inr (.inl (Fin.ext second))
  · exact .inr (.inr (Fin.ext third))

private theorem birth (reuse : Bool) : Insertable s2 (second reuse) child (some 0) := by
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

def trace (reuse : Bool) : Trace program 6 where
  state := states reuse
  notes := cutNotes (states reuse) (fun cut => eventActor (events reuse cut))
  event := events reuse
  start := rfl
  seed := rfl
  step cut valid := by
    have cuts : cut = 0 ∨ cut = 1 ∨ cut = 2 ∨ cut = 3 ∨ cut = 4 ∨ cut = 5 := by omega
    rcases cuts with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨⟨rfl, by simp, fun _ _ => trivial⟩, rfl⟩, rfl⟩
    · exact ⟨.begin s1 0 (fresh holder none) view rfl rfl (by change some _ ≠ none; simp)
        ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩, rfl⟩
    · cases reuse
      · exact ⟨.iter s2 _ 0 { (fresh holder none : F) with phase := .reloading (.waiting 1) [] view }
          (.waiting 1) [] view (.retire 2) .different rfl rfl
          ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
          (.instantiate s2 0 (.waiting 1) child 2 rfl (birth false)), rfl⟩
      · exact ⟨.iter s2 _ 0 { (fresh holder none : F) with phase := .reloading (.waiting 1) [] view }
          (.waiting 1) [] view (.retire 1) .same rfl rfl
          ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
          (.instantiate s2 0 (.waiting 1) child 1 rfl (birth true)), rfl⟩
    · cases reuse
      · exact ⟨.finish (s3 false) _ 0
          { (fresh holder none : F) with phase := .reloading .different [.retire 2] view }
          .different [.retire 2] view (.restrict 0 ()) rfl rfl
          ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
          (.provide _ _ _ { (fresh holder none : F) with phase := .reloading .different [.retire 2] view }
            () (value false) rfl rfl rfl rfl), rfl⟩
      · exact ⟨.finish (s3 true) _ 0
          { (fresh holder none : F) with phase := .reloading .same [.retire 1] view }
          .same [.retire 1] view (.restrict 0 ()) rfl rfl
          ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
          (.provide _ _ _ { (fresh holder none : F) with phase := .reloading .same [.retire 1] view }
            () (value true) rfl rfl rfl rfl), rfl⟩
    · cases reuse
      · exact ⟨.begin (s4 false) 2 (fresh child (some 0)) view rfl rfl (by change some _ ≠ none; simp)
          ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩, rfl⟩
      · exact ⟨.begin (s4 true) 1 (fresh child (some 0)) view rfl rfl (by change some _ ≠ none; simp)
          ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩, rfl⟩
    · cases reuse
      · exact ⟨.finish (s5 false) _ 2 { (fresh child (some 0) : F) with phase := .reloading .idle [] view }
          .idle [] view .unit rfl rfl ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩ (.unit _ _ _ rfl), rfl⟩
      · exact ⟨.finish (s5 true) _ 1 { (fresh child (some 0) : F) with phase := .reloading .idle [] view }
          .idle [] view .unit rfl rfl ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩ (.unit _ _ _ rfl), rfl⟩

/-! ## Every hypothesis but freshness holds -/

def parentEnd (reuse : Bool) : F :=
  { (fresh holder none : F) with
    table := fun other => if other = () then some (value reuse) else none
    phase := .active [.restrict 0 (), .retire (second reuse)] view }

def childEnd : F := { (fresh child (some 0) : F) with phase := .active [.unit] view }

theorem quiet (reuse : Bool) : Progress.Quiet ((trace reuse).state 6) := by
  intro name row found
  cases reuse <;> rcases name_cases name with rfl | rfl | rfl
  · have known : (trace false).state 6 0 = some (parentEnd false) := rfl
    rw [known] at found
    cases Option.some.inj found
    exact ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
  · exact absurd found (by change (none : Option F) ≠ _; simp)
  · have known : (trace false).state 6 2 = some childEnd := rfl
    rw [known] at found
    cases Option.some.inj found
    exact ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
  · have known : (trace true).state 6 0 = some (parentEnd true) := rfl
    rw [known] at found
    cases Option.some.inj found
    exact ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
  · have known : (trace true).state 6 1 = some childEnd := rfl
    rw [known] at found
    cases Option.some.inj found
    exact ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
  · exact absurd found (by change (none : Option F) ≠ _; simp)

theorem roots_only (reuse : Bool) :
    GuardedCanonicalSchedule.RootOnlyInput (GuardedBirthAddresses.orchestrationInput (trace reuse)) := by
  rw [GuardedCanonicalSchedule.root_only_input_iff_root_targets]
  intro cut bounded name command
  exfalso
  have cuts : cut = 0 ∨ cut = 1 ∨ cut = 2 ∨ cut = 3 ∨ cut = 4 ∨ cut = 5 := by omega
  change events reuse cut = _ ∨ events reuse cut = _ at command
  cases reuse <;> rcases cuts with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [events] at command

theorem same_roots : originalRoots (trace true) = originalRoots (trace false) := rfl

/-- The history that draws 2 has fresh draws. -/
theorem fresh_without_reuse : NominalConfluence.DrawsFresh nominal (trace false) := by
  intro time bounded row c word committed found reloading name vacant present
  have cuts : time = 0 ∨ time = 1 ∨ time = 2 ∨ time = 3 ∨ time = 4 ∨ time = 5 := by omega
  rcases cuts with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases name_cases name with rfl | rfl | rfl
  all_goals first
    | exact absurd vacant (fun same => Option.noConfusion same)
    | exact absurd rfl present
    | exact Option.noConfusion found
    | skip
  have known : (trace false).state 2 ((trace false).actor 2) =
      some { (fresh holder none : F) with phase := .reloading (.waiting 1) [] view } := rfl
  rw [known] at found
  cases Option.some.inj found
  cases reloading
  change ¬ ((1 : Name) = 2)
  decide

/-- The history that draws 1 does not: its code already mentions 1. -/
theorem stale_with_reuse : ¬ NominalConfluence.DrawsFresh nominal (trace true) := by
  intro freshDraws
  exact freshDraws 2 (by decide) { (fresh holder none : F) with phase := .reloading (.waiting 1) [] view }
    (.waiting 1) [] view rfl rfl 1 rfl (fun same => Option.noConfusion same) rfl

theorem published (reuse : Bool) :
    StageRecovery.tableAt ((trace reuse).state 6) 0 () = some (value reuse) := by
  cases reuse <;> rfl

theorem tables_disagree :
    ¬ ∃ p : Renaming.Permutation Name, ∀ name key, Iterators.OptionRel (TypedCoeffectReplay.setoid observe).r
      (StageRecovery.tableAt ((trace true).state 6) name key)
      (StageRecovery.tableAt ((trace false).state 6) (p.toFun name) key) := by
  rintro ⟨names, matched⟩
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

/-- With freshness removed, the conclusion of
`nominal_root_only_confluence` fails although every other hypothesis
holds for both histories. -/
theorem fresh_draws_necessary :
    (∀ reuse, Progress.Quiet ((trace reuse).state 6)) ∧
      (∀ reuse, GuardedCanonicalSchedule.RootOnlyInput (GuardedBirthAddresses.orchestrationInput (trace reuse))) ∧
      originalRoots (trace true) = originalRoots (trace false) ∧
      NominalConfluence.DrawsFresh nominal (trace false) ∧ ¬ NominalConfluence.DrawsFresh nominal (trace true) ∧
      ¬ ∃ p : Renaming.Permutation Name, ∀ name key, Iterators.OptionRel (TypedCoeffectReplay.setoid observe).r
        (StageRecovery.tableAt ((trace true).state 6) name key)
        (StageRecovery.tableAt ((trace false).state 6) (p.toFun name) key) :=
  ⟨quiet, roots_only, same_roots, fresh_without_reuse, stale_with_reuse, tables_disagree⟩

/-! ## The same boundary with child commands -/

namespace WithChildCommands
open EquivariantReuseCounterexample (parent)

private theorem name_cases' (name : Name) : name = 0 ∨ name = 1 ∨ name = 2 := by
  have within := name.isLt
  have values : name.val = 0 ∨ name.val = 1 ∨ name.val = 2 := by omega
  rcases values with first | second | third
  · exact .inl (Fin.ext first)
  · exact .inr (.inl (Fin.ext second))
  · exact .inr (.inr (Fin.ext third))

/-- Without reuse every birth in `EquivariantReuseCounterexample` is fresh. -/
theorem fresh_without_reuse :
    NominalConfluence.DrawsFresh nominal (EquivariantReuseCounterexample.trace false) := by
  intro time bounded row c word committed found reloading name vacant present
  have cuts : time = 0 ∨ time = 1 ∨ time = 2 ∨ time = 3 ∨ time = 4 ∨ time = 5 ∨ time = 6 ∨ time = 7 := by omega
  rcases cuts with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases name_cases' name with rfl | rfl | rfl
  all_goals first
    | exact absurd vacant (fun same => Option.noConfusion same)
    | exact absurd rfl present
    | exact Option.noConfusion found
    | skip
  · have known : (EquivariantReuseCounterexample.trace false).state 2
        ((EquivariantReuseCounterexample.trace false).actor 2) =
        some { (fresh parent none : F) with phase := .reloading .start [] view } := rfl
    rw [known] at found
    cases Option.some.inj found
    cases reloading
    exact id
  · have known : (EquivariantReuseCounterexample.trace false).state 5
        ((EquivariantReuseCounterexample.trace false).actor 5) =
        some { (fresh parent none : F) with phase := .reloading (.waiting 1) [.retire 1] view } := rfl
    rw [known] at found
    cases Option.some.inj found
    cases reloading
    change ¬ ((1 : Name) = 2)
    decide

/-- With reuse the second birth draws the name its parent's code holds. -/
theorem stale_with_reuse :
    ¬ NominalConfluence.DrawsFresh nominal (EquivariantReuseCounterexample.trace true) := by
  intro freshDraws
  exact freshDraws 5 (by decide) { (fresh parent none : F) with phase := .reloading (.waiting 1) [.retire 1] view }
    (.waiting 1) [.retire 1] view rfl rfl 1 rfl (fun same => Option.noConfusion same) rfl

theorem tables_disagree :
    ¬ ∃ p : Renaming.Permutation Name, ∀ name key, Iterators.OptionRel (TypedCoeffectReplay.setoid observe).r
      (StageRecovery.tableAt ((EquivariantReuseCounterexample.trace true).state 8) name key)
      (StageRecovery.tableAt ((EquivariantReuseCounterexample.trace false).state 8) (p.toFun name) key) := by
  rintro ⟨names, matched⟩
  have atParent := matched 0 ()
  rw [EquivariantReuseCounterexample.published true] at atParent
  rcases name_cases' (names.toFun 0) with image | image | image <;> rw [image] at atParent
  · rw [EquivariantReuseCounterexample.published false] at atParent
    obtain ⟨same, distinct⟩ := atParent
    cases same
    change (if true = true then 1 else 2 : Nat) = (if false = true then 1 else 2) at distinct
    simp at distinct
  · exact atParent
  · exact atParent

/-- Every hypothesis of `nominal_open_confluence` holds for both histories
except freshness of the second history's reused draw, and the conclusion
fails. -/
theorem fresh_draws_necessary :
    (∀ reuse, ¬ Nonempty (ClosedEpisode (EquivariantReuseCounterexample.trace reuse))) ∧
      (∀ reuse, Progress.Quiet ((EquivariantReuseCounterexample.trace reuse).state 8)) ∧
      GuardedBirthAddresses.orchestrationInput (EquivariantReuseCounterexample.trace true) =
        GuardedBirthAddresses.orchestrationInput (EquivariantReuseCounterexample.trace false) ∧
      NominalConfluence.DrawsFresh nominal (EquivariantReuseCounterexample.trace false) ∧
      ¬ NominalConfluence.DrawsFresh nominal (EquivariantReuseCounterexample.trace true) ∧
      ¬ ∃ p : Renaming.Permutation Name, ∀ name key, Iterators.OptionRel (TypedCoeffectReplay.setoid observe).r
        (StageRecovery.tableAt ((EquivariantReuseCounterexample.trace true).state 8) name key)
        (StageRecovery.tableAt ((EquivariantReuseCounterexample.trace false).state 8) (p.toFun name) key) :=
  ⟨EquivariantReuseCounterexample.open_only, EquivariantReuseCounterexample.quiet,
    EquivariantReuseCounterexample.same_input, fresh_without_reuse, stale_with_reuse, tables_disagree⟩

end WithChildCommands

end Cordis.Repairs.FreshDrawsNecessary
