import Cordis.Repairs.GuardedHistory

/-! Transport of registries, rules, and guarded histories along a map of
program codes. No rule inspects a code except to read an entry, to run
the current instruction, and to store the selected continuation, so a
code map that commutes with the program at the actual landings carries
every guarded history to a history of the image program.
It follows the pattern of the repository's renaming transport in
`GuardedRenaming`. -/
namespace Cordis.Repairs.CodeMap
open Calculus Stages LegalHistory GuardedHistory
open IncarnationReplay (Capture)
open Vestigial (CutNotes noteStep eventActor)
universe u
variable {Name Key Value Code Code' Error : Type u}

section Shapes
variable (f : Code → Code')

def component (c : Component Key Code) : Component Key Code' := ⟨c.requires, c.provides, f c.entry⟩

def phase {Undo : Type u} : Phase Name Key Code Undo → Phase Name Key Code' Undo
  | .inactive => .inactive
  | .reloading code accumulator view => .reloading (f code) accumulator view
  | .active accumulator view => .active accumulator view
  | .unloading accumulator view => .unloading accumulator view

def fiber {Undo : Type u} (row : Fiber Name Key Value Code Undo Error) : Fiber Name Key Value Code' Undo Error :=
  ⟨component f row.component, row.parent, row.table, row.retired, phase f row.phase⟩

def registry {Undo : Type u} (r : Registry Name Key Value Code Undo Error) : Registry Name Key Value Code' Undo Error :=
  fun name => (r name).map (fiber f)

def command : OrchestrationSorting.Command Name Key Code → OrchestrationSorting.Command Name Key Code'
  | .insert name c => .insert name (component f c)
  | .retire name => .retire name
  | .remove name => .remove name

def event : Event Name Key Code → Event Name Key Code'
  | .command c => .command (command f c)
  | .lifecycle kind actor => .lifecycle kind actor

def action : Stages.Action Name Key Value Code Error → Stages.Action Name Key Value Code' Error
  | .unit => .unit
  | .provide key value => .provide key value
  | .operate key run => .operate key run
  | .instantiate c => .instantiate (component f c)

end Shapes

section Laws
variable {f : Code → Code'} {Undo : Type u}

@[simp] theorem component_requires (c : Component Key Code) : (component f c).requires = c.requires := rfl
@[simp] theorem component_provides (c : Component Key Code) : (component f c).provides = c.provides := rfl
@[simp] theorem component_entry (c : Component Key Code) : (component f c).entry = f c.entry := rfl
@[simp] theorem fiber_component (row : Fiber Name Key Value Code Undo Error) :
    (fiber f row).component = component f row.component := rfl
@[simp] theorem fiber_parent (row : Fiber Name Key Value Code Undo Error) : (fiber f row).parent = row.parent := rfl
@[simp] theorem fiber_table (row : Fiber Name Key Value Code Undo Error) : (fiber f row).table = row.table := rfl
@[simp] theorem fiber_retired (row : Fiber Name Key Value Code Undo Error) : (fiber f row).retired = row.retired := rfl
@[simp] theorem fiber_phase (row : Fiber Name Key Value Code Undo Error) : (fiber f row).phase = phase f row.phase := rfl

@[simp] theorem phase_committed (p : Phase Name Key Code Undo) : (phase f p).committed = p.committed := by
  cases p <;> rfl

@[simp] theorem phase_accumulator (p : Phase Name Key Code Undo) : (phase f p).accumulator = p.accumulator := by
  cases p <;> rfl

@[simp] theorem phase_available (p : Phase Name Key Code Undo) : (phase f p).available ↔ p.available := by
  cases p <;> rfl

@[simp] theorem phase_inactive (p : Phase Name Key Code Undo) : phase f p = .inactive ↔ p = .inactive := by
  cases p <;> simp [phase]

@[simp] theorem registry_apply (r : Registry Name Key Value Code Undo Error) (name : Name) :
    registry f r name = (r name).map (fiber f) := rfl

theorem registry_none (r : Registry Name Key Value Code Undo Error) (name : Name) :
    registry f r name = none ↔ r name = none := by
  simp

@[simp] theorem registry_empty : registry f (fun _ => none : Registry Name Key Value Code Undo Error) = fun _ => none := rfl

@[simp] theorem eventActor_event (e : Event Name Key Code) : eventActor (event f e) = eventActor e := by
  cases e with
  | command c => cases c <;> rfl
  | lifecycle => rfl

@[simp] theorem eventRule_event (e : Event Name Key Code) : eventRule (event f e) = eventRule e := by
  cases e with
  | command c => cases c <;> rfl
  | lifecycle => rfl

theorem fiber_fresh (c : Component Key Code) (parentName : Option Name) :
    fiber f (fresh c parentName : Fiber Name Key Value Code Undo Error) = fresh (component f c) parentName := rfl

theorem target_iff (r : Registry Name Key Value Code Undo Error) (name : Name) (view : View Name Key) :
    Target (registry f r) name view ↔ Target r name view := by
  unfold Target
  cases found : r name with
  | none => simp [found]
  | some row =>
    simp only [registry_apply, found, Option.map_some, fiber_retired, fiber_component, component_requires]
    refine and_congr Iff.rfl (forall_congr' fun key => imp_congr Iff.rfl ?_)
    cases r (view key) <;> simp

theorem relied_iff (r : Registry Name Key Value Code Undo Error) (name : Name) :
    Relied (registry f r) name ↔ Relied r name := by
  unfold Relied
  refine exists_congr fun consumer => and_congr Iff.rfl ?_
  cases found : r consumer <;> simp [found]

theorem insertable_iff [DecidableEq Name] (r : Registry Name Key Value Code Undo Error) (name : Name)
    (c : Component Key Code) (parentName : Option Name) :
    Insertable (registry f r) name (component f c) parentName ↔ Insertable r name c parentName := by
  unfold Insertable
  refine and_congr (registry_none r name) (and_congr ?_ ?_)
  · exact forall_congr' fun p => imp_congr Iff.rfl (not_congr (registry_none r p))
  · refine forall_congr' fun other => forall_congr' fun key => ?_
    cases found : r other <;> simp [found]

theorem removable_iff (r : Registry Name Key Value Code Undo Error) (name : Name) :
    Removable (registry f r) name ↔ Removable r name := by
  unfold Removable
  cases found : r name with
  | none => simp [found]
  | some row =>
    simp only [registry_apply, found, Option.map_some, fiber_retired, fiber_phase, phase_inactive, fiber_table]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun child => ?_)))
    cases r child <;> simp

variable [DecidableEq Name]

theorem registry_put (r : Registry Name Key Value Code Undo Error) (name : Name) (row : Fiber Name Key Value Code Undo Error) :
    registry f (put r name row) = put (registry f r) name (fiber f row) := by
  funext other
  by_cases same : other = name <;> simp [put, same]

theorem registry_erase (r : Registry Name Key Value Code Undo Error) (name : Name) :
    registry f (erase r name) = erase (registry f r) name := by
  funext other
  by_cases same : other = name <;> simp [erase, same]

theorem registry_modify (r : Registry Name Key Value Code Undo Error) (name : Name)
    (change : Fiber Name Key Value Code Undo Error → Fiber Name Key Value Code Undo Error)
    (change' : Fiber Name Key Value Code' Undo Error → Fiber Name Key Value Code' Undo Error)
    (commutes : ∀ row, fiber f (change row) = change' (fiber f row)) :
    registry f (Calculus.modify r name change) = Calculus.modify (registry f r) name change' := by
  funext other
  by_cases same : other = name
  · subst other
    cases found : r name <;> simp [Calculus.modify, found, commutes]
  · simp [Calculus.modify, same]

theorem registry_mark (r : Registry Name Key Value Code Undo Error) (name : Name) (p : Phase Name Key Code Undo) :
    registry f (mark r name p) = mark (registry f r) name (phase f p) :=
  registry_modify r name _ _ (fun _ => rfl)

theorem registry_retire (r : Registry Name Key Value Code Undo Error) (name : Name) :
    registry f (retire r name) = retire (registry f r) name :=
  registry_modify r name _ _ (fun _ => rfl)

end Laws

section StageLaws
variable {f : Code → Code'}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "R'" => Registry Name Key Value Code' (Inverse Name Key Value) Error

theorem saved_registry (r : R) : PartialReplayRegistry.saved (registry f r) = PartialReplayRegistry.saved r := by
  funext name
  cases found : r name <;> simp [PartialReplayRegistry.saved, found]

theorem bindingOwner_registry (r : R) (name : Name) (key : Key) :
    bindingOwner (registry f r) name key = bindingOwner r name key := by
  unfold bindingOwner
  cases found : r name with
  | none => simp [found]
  | some row =>
    simp only [registry_apply, found, Option.map_some]
    cases row with
    | mk c p t rt ph => cases ph <;> rfl

theorem location_registry (r : R) (name : Name) (key : Key) :
    location (registry f r) name key = location r name key := by
  unfold location
  rw [bindingOwner_registry]
  congr 1
  funext owner
  cases h : r owner <;> simp [h]

variable [DecidableEq Name] [DecidableEq Key]

theorem registry_write (r : R) (owner : Name) (key : Key) (v : Option Value) :
    registry f (write r owner key v) = write (registry f r) owner key v :=
  registry_modify r owner _ _ (fun _ => rfl)

theorem registry_undo (token : Inverse Name Key Value) (r : R) :
    registry f (Stages.undo token r) = Stages.undo token (registry f r) := by
  cases token with
  | unit => rfl
  | restrict owner key => exact registry_write r owner key none
  | operate owner key inverse => exact registry_modify r owner _ _ (fun _ => rfl)
  | retire child => exact registry_retire r child

theorem registry_discharge (word : List (Inverse Name Key Value)) (r : R) :
    registry f (discharge Stages.undo word r) = discharge Stages.undo word (registry f r) := by
  induction word generalizing r with
  | nil => rfl
  | cons token rest ih => simp only [discharge, ih, registry_undo]

theorem registry_capture (live : Name → Option Nat) (capture : Capture Name Key Value) (r : R) :
    registry f (capture.apply live r) = capture.apply live (registry f r) := by
  unfold Capture.apply
  cases capture.token with
  | retire child =>
    by_cases matched : live child = some capture.index <;> simp only [matched, if_true, if_false]
    · exact registry_retire r child
  | _ => exact registry_undo _ r

theorem registry_replay (live : Name → Option Nat) (word : List (Capture Name Key Value)) (r : R) :
    registry f (IncarnationReplay.replay live word r) = IncarnationReplay.replay live word (registry f r) := by
  induction word generalizing r with
  | nil => rfl
  | cons capture rest ih => simp only [IncarnationReplay.replay, ih, registry_capture]

omit [DecidableEq Key] in
theorem noteStep_registry (before after : R) (actor : Name) (stamp : Nat) (notes : CutNotes Name Key Value) :
    noteStep (registry f before) (registry f after) actor stamp notes = noteStep before after actor stamp notes := by
  unfold noteStep IncarnationReplay.advance
  simp only [saved_registry]
  congr 1
  funext name
  cases found : after name <;> simp [found]

end StageLaws

section Rules
variable [DecidableEq Name] [DecidableEq Key] {f : Code → Code'}
variable {program : Code → Stages.Instruction Name Key Value Code Error}
variable {program' : Code' → Stages.Instruction Name Key Value Code' Error}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error

/-- The image program runs the same primitive and selects the image of
the same continuation after every outcome other than a child draw. -/
structure Compatible (f : Code → Code') (program : Code → Stages.Instruction Name Key Value Code Error)
    (program' : Code' → Stages.Instruction Name Key Value Code' Error) : Prop where
  action : ∀ c, (program' (f c)).action = action f (program c).action
  unit : ∀ c, (program' (f c)).next .unit = ((program c).next .unit).map f
  value : ∀ c v, (program' (f c)).next (.value v) = ((program c).next (.value v)).map f

/-- Agreement of the continuations after one particular child draw. -/
def ChildAgrees (f : Code → Code') (program : Code → Stages.Instruction Name Key Value Code Error)
    (program' : Code' → Stages.Instruction Name Key Value Code' Error) (c : Code) (child : Name) : Prop :=
  (program' (f c)).next (.child child) = ((program c).next (.child child)).map f

/-- Every name that appears at a step drawn by a reloading actor is a
draw at which the continuations agree. -/
def DrawsAgree (f : Code → Code') (program : Code → Stages.Instruction Name Key Value Code Error)
    (program' : Code' → Stages.Instruction Name Key Value Code' Error) (before after : R) (actor : Name) : Prop :=
  ∀ row c word view, before actor = some row → row.phase = .reloading c word view →
    ∀ child, before child = none → after child ≠ none → ChildAgrees f program program' c child

omit [DecidableEq Key] in
private theorem mark_present (s : R) (name other : Name) (p : Phase Name Key Code (Inverse Name Key Value)) :
    mark s name p other = none ↔ s other = none := by
  by_cases same : other = name
  · subst other; cases h : s name <;> simp [mark, Calculus.modify, h]
  · simp [mark, Calculus.modify, same]

theorem land_map (compatible : Compatible f program program') {actor : Name} {c : Code} {r s : R}
    {token : Inverse Name Key Value} {next : Option Code} (landed : Land program actor c r s token next)
    (draws : ∀ child, r child = none → s child ≠ none → ChildAgrees f program program' c child) :
    Land program' actor (f c) (registry f r) (registry f s) token (next.map f) := by
  cases landed with
  | unit _ _ _ chosen =>
    have step := Execution.unit (program := program') (result := fun code => (program' code).next)
      (registry f r) actor (f c) (by rw [compatible.action, chosen]; rfl)
    dsimp only at step
    rwa [compatible.unit] at step
  | provide _ _ _ row key v chosen present declared vacant =>
    have step := Execution.provide (program := program') (result := fun code => (program' code).next)
      (registry f r) actor (f c) (fiber f row) key v (by rw [compatible.action, chosen]; rfl)
      (by simp [present]) declared vacant
    dsimp only at step
    rw [compatible.value, ← registry_write] at step
    exact step
  | operate _ _ _ key run owner before after inverse v chosen located returned =>
    have step := Execution.operate (program := program') (result := fun code => (program' code).next)
      (registry f r) actor (f c) key run owner before after inverse v (by rw [compatible.action, chosen]; rfl)
      (by rw [location_registry]; exact located) returned
    dsimp only at step
    rw [compatible.value, ← registry_write] at step
    exact step
  | instantiate _ _ _ comp child chosen insertable =>
    have step := Execution.instantiate (program := program') (result := fun code => (program' code).next)
      (registry f r) actor (f c) (component f comp) child (by rw [compatible.action, chosen]; rfl)
      ((insertable_iff r child comp (some actor)).mpr insertable)
    have agrees := draws child insertable.1 (by simp [put])
    dsimp only at step
    rw [agrees, ← fiber_fresh, ← registry_put] at step
    exact step

theorem step_map (compatible : Compatible f program program') {rule : Labeled.Rule} {actor : Name} {r after : R}
    (step : Labeled.Step program rule actor r after) (draws : DrawsAgree f program program' r after actor) :
    Labeled.Step program' rule actor (registry f r) (registry f after) := by
  cases step with
  | insert _ _ comp parentName insertable =>
    rw [registry_put, fiber_fresh]
    exact .insert _ _ _ _ ((insertable_iff r actor comp parentName).mpr insertable)
  | retire _ _ present =>
    rw [registry_retire]
    exact .retire _ _ (by simpa using present)
  | remove _ _ removable =>
    rw [registry_erase]
    exact .remove _ _ ((removable_iff r actor).mpr removable)
  | begin _ _ row view found inactive errorFree target =>
    rw [registry_mark]
    exact .begin _ _ (fiber f row) view (by simp [found]) (by simp [inactive, phase])
      (by simpa using errorFree) ((target_iff r actor view).mpr target)
  | iter _ s _ row c word view inverse next found reloading target landed =>
    rw [registry_mark]
    exact .iter _ _ _ (fiber f row) (f c) word view inverse (f next) (by simp [found]) (by simp [reloading, phase])
      ((target_iff r actor view).mpr target)
      (land_map compatible landed fun child vacant present =>
        draws row c word view found reloading child vacant (by rwa [ne_eq, mark_present]))
  | finish _ s _ row c word view inverse found reloading target landed =>
    rw [registry_mark]
    exact .finish _ _ _ (fiber f row) (f c) word view inverse (by simp [found]) (by simp [reloading, phase])
      ((target_iff r actor view).mpr target)
      (land_map compatible landed fun child vacant present =>
        draws row c word view found reloading child vacant (by rwa [ne_eq, mark_present]))
  | divert _ s _ row c word view tail found reloading blocked route =>
    rw [registry_mark]
    refine .divert _ _ _ (fiber f row) (f c) word view tail (by simp [found]) (by simp [reloading, phase])
      (fun target => blocked ((target_iff r actor view).mp target)) ?_
    rcases route with ⟨rfl, rfl⟩ | ⟨inverse, next, landed, rfl⟩
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr ⟨inverse, next.map f, land_map compatible landed fun child vacant present =>
        draws row c word view found reloading child vacant (by rwa [ne_eq, mark_present]), rfl⟩
  | leave _ _ row word view found active blocked =>
    rw [registry_mark]
    exact .leave _ _ (fiber f row) word view (by simp [found]) (by simp [active, phase])
      (fun target => blocked ((target_iff r actor view).mp target))
  | unload _ _ row word view found unloading guard =>
    rw [registry_mark, registry_discharge]
    exact .unload _ _ (fiber f row) word view (by simp [found]) (by simp [unloading, phase])
      (fun relied => guard ((relied_iff r actor).mp relied))

omit [DecidableEq Key] in
theorem command_map {cmd : OrchestrationSorting.Command Name Key Code} {r s : R} (step : cmd.Step r s) :
    (command f cmd).Step (registry f r) (registry f s) := by
  obtain ⟨enabled, rfl⟩ := step
  cases cmd with
  | insert name comp =>
    exact ⟨(insertable_iff r name comp none).mpr enabled, by
      simp only [OrchestrationSorting.Command.apply, command, registry_put, fiber_fresh]⟩
  | retire name =>
    exact ⟨by simpa [OrchestrationSorting.Command.Enabled] using enabled, by
      simp only [OrchestrationSorting.Command.apply, command, registry_retire]⟩
  | remove name =>
    exact ⟨(removable_iff r name).mpr enabled, by
      simp only [OrchestrationSorting.Command.apply, command, registry_erase]⟩

theorem unload_map {actor : Name} {before after : R} {notes : CutNotes Name Key Value}
    (step : GuardedSuffix.Unload actor before notes after) :
    GuardedSuffix.Unload actor (registry f before) notes (registry f after) := by
  obtain ⟨row, view, found, unloading, guard, rfl⟩ := step
  refine ⟨fiber f row, view, by simp [found], by simp [unloading, phase],
    fun relied => guard ((relied_iff before actor).mp relied), ?_⟩
  rw [registry_mark, registry_replay]
  rfl

theorem suffix_map (compatible : Compatible f program program') {e : Event Name Key Code} {stamp : Nat}
    {before after : R} {notes recorded : CutNotes Name Key Value}
    (step : GuardedSuffix.Step program e stamp before notes after recorded)
    (draws : DrawsAgree f program program' before after (eventActor e)) :
    GuardedSuffix.Step program' (event f e) stamp (registry f before) notes (registry f after) recorded := by
  obtain ⟨transition, rfl⟩ := step
  refine ⟨?_, by rw [noteStep_registry, eventActor_event]⟩
  cases e with
  | command cmd => exact command_map transition
  | lifecycle kind actor =>
    cases kind with
    | unload => exact unload_map transition
    | _ => exact step_map compatible transition draws

/-- A guarded history of the source program, mapped code by code. -/
def mapTrace (compatible : Compatible f program program') {last : Nat} (trace : Trace program last)
    (draws : ∀ time, time < last →
      DrawsAgree f program program' (trace.state time) (trace.state (time + 1)) (trace.actor time)) :
    Trace program' last where
  state time := registry f (trace.state time)
  notes := trace.notes
  event time := event f (trace.event time)
  start := by rw [trace.start]; rfl
  seed := trace.seed
  step time bounded := suffix_map compatible (trace.step time bounded) (draws time bounded)

end Rules

end Cordis.Repairs.CodeMap
