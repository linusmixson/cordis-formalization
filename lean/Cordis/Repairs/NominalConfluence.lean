import Cordis.Repairs.CodeMap
import Cordis.Repairs.GuardedCanonicalSchedule

/-! Confluence for programs whose codes may store child names.

`ChildContinuations` asks that a birth's continuation ignore the drawn
name, which already excludes a program that records which child it
spawned. Here codes may carry names, under a renaming action with a
support, and the program need only commute with renaming. Each birth must
draw a name the parent's current code does not mention (`DrawsFresh`).
`EquivariantReuseCounterexample` shows this condition cannot be dropped.

The proof quotients codes by renaming. The quotient program satisfies
`ChildContinuations`, every history maps to a history of it, and the
repaired root-only confluence theorem applies there. Tables are not
touched by the map, so the endpoint tables agree up to a renaming.
All of the work is done by the repaired Theorem 80
(`confluence_of_root_only_input`); this file only supplies the quotient
on which it applies. -/
namespace Cordis.Repairs.NominalConfluence
open Calculus Stages LegalHistory GuardedHistory
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PaperObservationEquations (OperationRespects)
open PartialCoeffectIndependenceContracts (tableSetoid)
open TypedRegistry (Scalar encodeProgram)
universe u
variable {Name Key Code : Type u} {V : Key → Type u} {ops : CoeffectOperations V}
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false
local notation "P" => Renaming.Permutation Name

/-! ## History lemmas for code maps -/

section History
variable {Value Code' Error : Type u} {f : Code → Code'}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error

omit [DecidableEq Name] [DecidableEq Key] in
theorem rootAt_registry (r : R) (name : Name) :
    LegalHistory.rootAt (CodeMap.registry f r) name = LegalHistory.rootAt r name := by
  unfold LegalHistory.rootAt
  cases h : r name <;> simp [h]

omit [DecidableEq Name] [DecidableEq Key] in
theorem eventRoots_registry (r : R) (e : Event Name Key Code) :
    LegalHistory.eventRoots (CodeMap.registry f r) (CodeMap.event f e) =
      (LegalHistory.eventRoots r e).map (CodeMap.command f) := by
  cases e with
  | lifecycle => rfl
  | command c =>
    cases c with
    | insert => rfl
    | retire name =>
      simp only [CodeMap.event, CodeMap.command, LegalHistory.eventRoots, LegalHistory.commandRoots,
        rootAt_registry]
      split <;> rfl
    | remove name =>
      simp only [CodeMap.event, CodeMap.command, LegalHistory.eventRoots, LegalHistory.commandRoots,
        rootAt_registry]
      split <;> rfl

omit [DecidableEq Name] [DecidableEq Key] in
theorem tableAt_registry (r : R) (name : Name) (key : Key) :
    StageRecovery.tableAt (CodeMap.registry f r) name key = StageRecovery.tableAt r name key := by
  unfold StageRecovery.tableAt
  cases h : r name <;> simp [h]

omit [DecidableEq Key] in
theorem quiet_registry {r : R} (quiet : Progress.Quiet r) : Progress.Quiet (CodeMap.registry f r) := by
  intro name row found
  simp only [CodeMap.registry_apply, Option.map_eq_some_iff] at found
  obtain ⟨original, present, rfl⟩ := found
  have claim := quiet name original present
  cases phase : original.phase with
  | inactive =>
    rw [phase] at claim
    simp only [CodeMap.fiber_phase, phase, CodeMap.phase]
    exact fun view target => claim view ((CodeMap.target_iff r name view).mp target)
  | reloading => rw [phase] at claim; exact claim.elim
  | active word view =>
    rw [phase] at claim
    simp only [CodeMap.fiber_phase, phase, CodeMap.phase]
    exact (CodeMap.target_iff r name view).mpr claim
  | unloading => rw [phase] at claim; exact claim.elim

variable {program : Code → Stages.Instruction Name Key Value Code Error}
variable {program' : Code' → Stages.Instruction Name Key Value Code' Error}

theorem originalRoots_map (compatible : CodeMap.Compatible f program program') {last : Nat}
    (trace : Trace program last) draws :
    originalRoots (CodeMap.mapTrace compatible trace draws) = (originalRoots trace).map (CodeMap.command f) := by
  unfold originalRoots
  rw [List.map_flatMap]
  congr 1
  funext time
  exact eventRoots_registry _ _

theorem rootOnly_map (compatible : CodeMap.Compatible f program program') {last : Nat}
    (trace : Trace program last) draws
    (roots : GuardedCanonicalSchedule.RootOnlyInput (GuardedBirthAddresses.orchestrationInput trace)) :
    GuardedCanonicalSchedule.RootOnlyInput
      (GuardedBirthAddresses.orchestrationInput (CodeMap.mapTrace compatible trace draws)) := by
  rw [GuardedCanonicalSchedule.root_only_input_iff_root_targets] at roots ⊢
  intro cut bounded name command
  have original : trace.event cut = .command (.retire name) ∨ trace.event cut = .command (.remove name) := by
    change CodeMap.event f (trace.event cut) = _ ∨ CodeMap.event f (trace.event cut) = _ at command
    cases event : trace.event cut with
    | lifecycle => rw [event] at command; simp [CodeMap.event] at command
    | command c =>
      rw [event] at command
      cases c <;> simp_all [CodeMap.event, CodeMap.command]
  change LegalHistory.rootAt (CodeMap.registry f (trace.state cut)) name = true
  rw [rootAt_registry]
  exact roots cut bounded name original

end History

/-! ## Nominal programs -/

def renameAction (act : P → Code → Code) (χ : P) :
    TypedRegistry.Action Name ops Code → TypedRegistry.Action Name ops Code
  | .unit => .unit
  | .provide key value => .provide key value
  | .operate key name argument => .operate key name argument
  | .instantiate c => .instantiate { c with entry := act χ c.entry }

def renameOutcome (χ : P) : TypedRegistry.Outcome Name ops → TypedRegistry.Outcome Name ops
  | .unit => .unit
  | .provision key value => .provision key value
  | .operation key name outcome => .operation key name outcome
  | .child name => .child (χ.toFun name)

/-- Codes carry names under a renaming action with a support, and the
program commutes with renaming. -/
structure Nominal (program : Code → TypedRegistry.Instruction Name ops Code) where
  act : P → Code → Code
  act_trans : ∀ (χ ψ : P) c, act ψ (act χ c) = act (χ.trans ψ) c
  act_symm : ∀ (χ : P) c, act χ.symm (act χ c) = c
  supp : Code → Name → Prop
  fixes : ∀ (χ : P) c, (∀ n, supp c n → χ.toFun n = n) → act χ c = c
  supp_act : ∀ (χ : P) c n, supp (act χ c) (χ.toFun n) ↔ supp c n
  fresh : ∀ c, ∃ n, ¬ supp c n
  action : ∀ (χ : P) c, (program (act χ c)).action = renameAction act χ (program c).action
  next : ∀ (χ : P) c o, (program (act χ c)).next (renameOutcome χ o) = ((program c).next o).map (act χ)

/-- Every birth draws a name the parent's current code does not mention. -/
def DrawsFresh {program : Code → TypedRegistry.Instruction Name ops Code} (N : Nominal program) {last : Nat}
    (trace : Trace (encodeProgram program) last) : Prop :=
  ∀ time, time < last → ∀ row c word view, trace.state time (trace.actor time) = some row →
    row.phase = .reloading c word view → ∀ child, trace.state time child = none →
      trace.state (time + 1) child ≠ none → ¬ N.supp c child

section Quotient
variable {program : Code → TypedRegistry.Instruction Name ops Code} (N : Nominal program)

def orbit : Setoid Code where
  r c d := ∃ χ : P, N.act χ c = d
  iseqv :=
    { refl := fun c => (⟨Renaming.Permutation.identity, N.fixes _ c (fun _ _ => rfl)⟩ : ∃ χ : P, N.act χ c = c)
      symm := by
        rintro c d ⟨χ, rfl⟩
        exact ⟨χ.symm, N.act_symm χ c⟩
      trans := by
        rintro c d e ⟨χ, rfl⟩ ⟨ψ, rfl⟩
        exact ⟨χ.trans ψ, (N.act_trans χ ψ c).symm⟩ }

abbrev Orbit := Quotient (orbit N)

def quot (c : Code) : Orbit N := Quotient.mk (orbit N) c

theorem quot_act (χ : P) (c : Code) : quot N (N.act χ c) = quot N c := by
  apply Eq.symm
  apply Quotient.sound
  show ∃ ψ : P, N.act ψ c = N.act χ c
  exact ⟨χ, rfl⟩

def mapAction (a : TypedRegistry.Action Name ops Code) : TypedRegistry.Action Name ops (Orbit N) :=
  match a with
  | .unit => .unit
  | .provide key value => .provide key value
  | .operate key name argument => .operate key name argument
  | .instantiate c => .instantiate (CodeMap.component (quot N) c)

theorem mapAction_rename (χ : P) (a : TypedRegistry.Action Name ops Code) :
    mapAction N (renameAction N.act χ a) = mapAction N a := by
  cases a with
  | instantiate c =>
    simp only [renameAction, mapAction, CodeMap.component, quot_act]
  | _ => rfl

noncomputable def freshFor (c : Code) : Name := Classical.choose (N.fresh c)

theorem freshFor_spec (c : Code) : ¬ N.supp c (freshFor N c) := Classical.choose_spec (N.fresh c)

/-- The transposition of two names. -/
def transpose (a b : Name) : P where
  toFun n := if n = a then b else if n = b then a else n
  invFun n := if n = a then b else if n = b then a else n
  left_inv n := by
    by_cases ha : n = a <;> by_cases hb : n = b <;> simp_all
  right_inv n := by
    by_cases ha : n = a <;> by_cases hb : n = b <;> simp_all

/-- Two draws fresh for a code lead to continuations in the same orbit. -/
theorem fresh_draws_agree (c : Code) {b b' : Name} (fb : ¬ N.supp c b) (fb' : ¬ N.supp c b') :
    ((program c).next (.child b)).map (quot N) = ((program c).next (.child b')).map (quot N) := by
  let σ := transpose b b'
  have fixed : N.act σ c = c := by
    apply N.fixes
    intro n mentioned
    have nb : n ≠ b := fun same => fb (same ▸ mentioned)
    have nb' : n ≠ b' := fun same => fb' (same ▸ mentioned)
    simp [σ, transpose, nb, nb']
  have moved := N.next σ c (.child b)
  rw [fixed] at moved
  have image : renameOutcome (ops := ops) σ (.child b) = .child b' := by
    simp [renameOutcome, σ, transpose]
  rw [image] at moved
  rw [moved, Option.map_map]
  congr 1
  funext d
  exact (quot_act N σ d).symm

noncomputable def nextOn (c : Code) : TypedRegistry.Outcome Name ops → Option (Orbit N)
  | .child _ => ((program c).next (.child (freshFor N c))).map (quot N)
  | o => ((program c).next o).map (quot N)

theorem nextOn_respects (c d : Code) (related : (orbit N).r c d) : nextOn N c = nextOn N d := by
  obtain ⟨χ, rfl⟩ := related
  funext o
  have mapped (o : TypedRegistry.Outcome Name ops) :
      ((program (N.act χ c)).next (renameOutcome χ o)).map (quot N) = ((program c).next o).map (quot N) := by
    rw [N.next, Option.map_map]
    congr 1
    funext d
    exact quot_act N χ d
  cases o with
  | child b =>
    simp only [nextOn]
    let b₀ := χ.invFun (freshFor N (N.act χ c))
    have fresh₀ : ¬ N.supp c b₀ := by
      intro mentioned
      apply freshFor_spec N (N.act χ c)
      have := (N.supp_act χ c b₀).mpr mentioned
      simpa [b₀] using this
    have image : renameOutcome (ops := ops) χ (.child b₀) = .child (freshFor N (N.act χ c)) := by
      simp [renameOutcome, b₀]
    rw [← image, mapped, fresh_draws_agree N c (freshFor_spec N c) fresh₀]
  | unit => exact (mapped .unit).symm
  | provision key value => exact (mapped (.provision key value)).symm
  | operation key name outcome => exact (mapped (.operation key name outcome)).symm

/-- The quotient program: one code per orbit, and a birth's continuation
taken at a canonical fresh draw. -/
noncomputable def quotient : Orbit N → TypedRegistry.Instruction Name ops (Orbit N) :=
  fun x => ⟨Quotient.lift (fun c => mapAction N (program c).action) (by
      rintro c d ⟨χ, rfl⟩
      simp only [N.action, mapAction_rename]) x,
    Quotient.lift (nextOn N) (nextOn_respects N) x⟩

theorem quotient_action (c : Code) : (quotient N (quot N c)).action = mapAction N (program c).action := rfl

theorem quotient_next (c : Code) (o : TypedRegistry.Outcome Name ops) :
    (quotient N (quot N c)).next o = nextOn N c o := rfl

theorem quotient_child_continuations : GuardedLandingMatching.ChildContinuations (encodeProgram (quotient N)) := by
  intro x _ _ child other
  induction x using Quotient.ind
  rfl

theorem compatible :
    CodeMap.Compatible (quot N) (encodeProgram program) (encodeProgram (quotient N)) where
  action c := by
    show TypedRegistry.encodeAction ops (mapAction N (program c).action) =
      CodeMap.action (quot N) (TypedRegistry.encodeAction ops (program c).action)
    generalize (program c).action = a
    cases a <;> rfl
  unit c := rfl
  value c v := by
    change ((TypedRegistry.decodeOutcome ops (.value v)).bind (quotient N (quot N c)).next) =
      ((TypedRegistry.decodeOutcome ops (.value v)).bind (program c).next).map (quot N)
    rcases v with (none | ⟨key, value⟩) | (⟨key, value⟩ | ⟨key, name, outcome⟩) <;> rfl

theorem draws_agree {last : Nat} {trace : Trace (encodeProgram program) last} (fresh : DrawsFresh N trace)
    (time : Nat) (bounded : time < last) :
    CodeMap.DrawsAgree (quot N) (encodeProgram program) (encodeProgram (quotient N))
      (trace.state time) (trace.state (time + 1)) (trace.actor time) := by
  intro row c word view found reloading child vacant present
  change ((TypedRegistry.decodeOutcome ops (.child child)).bind (quotient N (quot N c)).next) =
    ((TypedRegistry.decodeOutcome ops (.child child)).bind (program c).next).map (quot N)
  simp only [TypedRegistry.decodeOutcome, Option.bind_some, quotient_next, nextOn]
  exact fresh_draws_agree N c (freshFor_spec N c) (fresh time bounded row c word view found reloading child vacant present)

end Quotient

/-! ## The theorem -/

/-- Root-only confluence for name-carrying codes. Two quiet histories of a
renaming-equivariant program, with equal root commands, only root-targeted
child-free commands, and fresh draws at every birth, have endpoint tables
that agree up to a renaming of their owners. -/
theorem nominal_root_only_confluence {program : Code → TypedRegistry.Instruction Name ops Code}
    (N : Nominal program) {last rightLength : Nat}
    (left : Trace (encodeProgram program) last) (right : Trace (encodeProgram program) rightLength)
    (leftFresh : DrawsFresh N left) (rightFresh : DrawsFresh N right)
    (leftQuiet : Progress.Quiet (left.state last)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (leftRoots : GuardedCanonicalSchedule.RootOnlyInput (GuardedBirthAddresses.orchestrationInput left))
    (rightRoots : GuardedCanonicalSchedule.RootOnlyInput (GuardedBirthAddresses.orchestrationInput right))
    (commands : originalRoots left = originalRoots right)
    (observe : ∀ key, Setoid (V key)) (contracts : GuardedCanonicalSchedule.OperationContracts ops observe) :
    ∃ p : P, ∀ name key, Iterators.OptionRel (TypedCoeffectReplay.setoid observe).r
      (StageRecovery.tableAt (left.state last) name key)
      (StageRecovery.tableAt (right.state rightLength) (p.toFun name) key) := by
  let first := CodeMap.mapTrace (compatible N) left (draws_agree N leftFresh)
  let second := CodeMap.mapTrace (compatible N) right (draws_agree N rightFresh)
  have agreement := GuardedCanonicalSchedule.confluence_of_root_only_input first second
    (quiet_registry leftQuiet) (quiet_registry rightQuiet)
    (rootOnly_map (compatible N) left _ leftRoots) (rootOnly_map (compatible N) right _ rightRoots)
    (by rw [originalRoots_map, originalRoots_map, commands])
    (quotient_child_continuations N) observe contracts.recovery contracts.commutative contracts.respect
  obtain ⟨p, tables⟩ := agreement.tables observe
  refine ⟨p, fun name key => ?_⟩
  have compared := tables name key
  change Iterators.OptionRel _ (StageRecovery.tableAt (CodeMap.registry (quot N) (left.state last)) name key)
    (StageRecovery.tableAt (CodeMap.registry (quot N) (right.state rightLength)) (p.toFun name) key) at compared
  rwa [tableAt_registry, tableAt_registry] at compared

end Cordis.Repairs.NominalConfluence
