import Cordis.Repairs.GuardedCanonicalOrder
import Cordis.Repairs.GuardedCommandAlignment
import Cordis.Repairs.GuardedConfluence

/-! Select a canonical addressed schedule from the legal histories over
the fixed name set. Only the event order is canonical; draws stay local
to the witnessing history. -/
namespace Cordis.Repairs.GuardedCanonicalSchedule
open Calculus Stages LegalHistory GuardedHistory
open GuardedBirthAddresses GuardedAddressSchedule GuardedCommandAlignment
open OrchestrationSorting (Command)

universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
variable {program : Code → Instruction Name Key Value Code Error} {last : Nat}

private def pairAddressData : Nat → Nat → Nat
  | 0, stage => 2 * stage + 1
  | depth + 1, stage => 2 * pairAddressData depth stage

private theorem pairAddressData_injective {a b i j : Nat}
    (same : pairAddressData a i = pairAddressData b j) : a = b ∧ i = j := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => simp [pairAddressData] at same; omega
    | succ b =>
      simp only [pairAddressData] at same
      omega
  | succ a ih =>
    cases b with
    | zero =>
      simp only [pairAddressData] at same
      omega
    | succ b =>
      simp only [pairAddressData] at same
      obtain ⟨rfl, equal⟩ := ih (by omega : pairAddressData a i = pairAddressData b j)
      exact ⟨rfl, equal⟩

private def addressRank : Address → Nat
  | .root ordinal => 2 * ordinal
  | .child parent stage => 2 * pairAddressData (addressRank parent) stage + 1

private theorem addressRank_injective {first second : Address} (same : addressRank first = addressRank second) :
    first = second := by
  induction first generalizing second with
  | root ordinal =>
    cases second <;> simp only [addressRank, Address.root.injEq] at * <;> omega
  | child parent stage ih =>
    cases second with
    | root => simp only [addressRank] at same; omega
    | child other index =>
      simp only [addressRank] at same
      obtain ⟨equal, rfl⟩ := pairAddressData_injective
        (by omega : pairAddressData (addressRank parent) stage = pairAddressData (addressRank other) index)
      exact congrArg (fun path => Address.child path stage) (ih equal)

private def lifecycleRank : Lifecycle → Nat
  | .begin => 3
  | .iter => 4
  | .finish => 5
  | .divert => 6
  | .leave => 7
  | .unload => 8

private def eventRank {Key Code : Type u} : Option (AddressedEvent Key Code) → Nat
  | none => 0
  | some (.insert _) => 1
  | some (.retire path) => 9 * addressRank path + 2
  | some (.remove path) => 9 * addressRank path + 9
  | some (.lifecycle kind path) => 9 * addressRank path + lifecycleRank kind

private theorem equal_rank {Key Code : Type u} {first second : Option (AddressedEvent Key Code)}
    (same : eventRank first = eventRank second) :
    first = second ∨ ∃ a b, first = some (.insert a) ∧ second = some (.insert b) := by
  cases first with
  | none =>
    cases second with
    | none => exact .inl rfl
    | some event =>
      cases event <;> try (simp only [eventRank] at same; omega)
      rename_i kind _
      cases kind <;> simp only [eventRank, lifecycleRank] at same <;> omega
  | some first =>
    cases second with
    | none =>
      cases first <;> try (simp only [eventRank] at same; omega)
      rename_i kind _
      cases kind <;> simp only [eventRank, lifecycleRank] at same <;> omega
    | some second =>
      cases first with
      | insert a =>
        cases second with
        | insert b => exact .inr ⟨a, b, rfl, rfl⟩
        | retire | remove => simp only [eventRank] at same; omega
        | lifecycle kind path =>
          cases kind <;> simp only [eventRank, lifecycleRank] at same <;> omega
      | retire path =>
        cases second with
        | retire other =>
          apply Or.inl
          simp only [eventRank] at same
          rw [addressRank_injective (by omega : addressRank path = addressRank other)]
        | insert | remove => simp only [eventRank] at same; omega
        | lifecycle kind other =>
          cases kind <;> simp only [eventRank, lifecycleRank] at same <;> omega
      | remove path =>
        cases second with
        | remove other =>
          apply Or.inl
          simp only [eventRank] at same
          rw [addressRank_injective (by omega : addressRank path = addressRank other)]
        | insert | retire => simp only [eventRank] at same; omega
        | lifecycle kind other =>
          cases kind <;> simp only [eventRank, lifecycleRank] at same <;> omega
      | lifecycle kind path =>
        cases second with
        | insert | retire | remove =>
          cases kind <;> simp only [eventRank, lifecycleRank] at same <;> omega
        | lifecycle otherKind other =>
          have equal : kind = otherKind := by
            cases kind <;> cases otherKind <;> simp only [eventRank, lifecycleRank] at same <;> first | rfl | omega
          subst otherKind
          have address : addressRank path = addressRank other := by simp only [eventRank] at same; omega
          exact .inl (by rw [addressRank_injective address])

/-- The command input fixes insertion payloads, while each other event is
ordered by its kind and the recursive address of its actual actor. -/
noncomputable def priorityWord (trace : Trace program last) : List Nat :=
  (List.range last).map fun cut => eventRank (addressedEventAt trace cut)

private theorem priorityWord_length (trace : Trace program last) : (priorityWord trace).length = last := by
  simp [priorityWord]

private theorem insertion_of_address {trace : Trace program last} {cut : Nat} {component : Component Key Code}
    (address : addressedEventAt trace cut = some (.insert component)) :
    ∃ name, trace.event cut = .command (.insert name component) := by
  cases event : trace.event cut with
  | lifecycle kind actor =>
    simp only [addressedEventAt, event] at address
    cases found : actorAddress trace cut <;> simp [found] at address
  | command command =>
    cases command with
    | insert name payload =>
      have equal : payload = component := by simpa [addressedEventAt, event] using address
      exact ⟨name, by rw [equal]⟩
    | retire | remove =>
      simp only [addressedEventAt, event] at address
      cases found : actorAddress trace cut <;> simp [found] at address

theorem addressed_order_of_equal_priority_words (left right : Trace program last)
    (input : orchestrationInput left = orchestrationInput right) (words : priorityWord left = priorityWord right) :
    ∀ cut, cut < last → addressedEventAt left cut = addressedEventAt right cut := by
  intro cut
  induction cut using Nat.strongRecOn with
  | ind cut ih =>
    intro bounded
    have key := congrArg (fun word : List Nat => word[cut]?) words
    have equal : eventRank (addressedEventAt left cut) = eventRank (addressedEventAt right cut) := by
      simpa [priorityWord, List.getElem?_map, List.getElem?_range, bounded] using key
    rcases equal_rank equal with same | ⟨first, second, leftInsert, rightInsert⟩
    · exact same
    · obtain ⟨name, leftEvent⟩ := insertion_of_address leftInsert
      obtain ⟨other, rightEvent⟩ := insertion_of_address rightInsert
      have command := next_commands_agree left right (span := 0) bounded bounded
        (fun i earlier => ih i earlier (by omega)) input leftEvent rightEvent (fun i lower upper => by omega)
      have payload : first = second := by
        simpa [commandAt, commandEventAddress, leftEvent, rightEvent] using congrArg (Option.map commandEventAddress) command
      rw [leftInsert, rightInsert, payload]

/-- Candidates are quiet, open, legal executions with the same addressed
input. A command may wait for a birth, and it retains its position in the
input relative to all other commands. -/
def Candidate (input : List (AddressedCommand Name Key Code)) (trace : Trace program last) : Prop :=
  (¬ Nonempty (ClosedEpisode trace)) ∧ Progress.Quiet (trace.state last) ∧
    CommandsAtBirthBarriers trace ∧ orchestrationInput trace = input

def Canonical (input : List (AddressedCommand Name Key Code)) (trace : Trace program last) : Prop :=
  Candidate input trace ∧ ∀ other : Trace program last, Candidate input other → priorityWord trace ≤ priorityWord other

/-- Existence over the original name set, witnessed first by actual
command exchanges and then by minimization over legal candidates. -/
theorem exists_canonical (trace : Trace program last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last)) :
    ∃ result : Trace program last, Canonical (orchestrationInput trace) result := by
  obtain ⟨earlier, _, barriers, _, input, _, _, earlierOpen, earlierQuiet⟩ :=
    push_commands_to_birth_barriers trace opened quiet
  let realizes (word : List Nat) :=
    ∃ result : Trace program last, Candidate (orchestrationInput trace) result ∧ priorityWord result = word
  obtain ⟨least, _, ⟨result, candidate, rfl⟩, minimal⟩ := least_priority_word last realizes
    ⟨_, priorityWord_length earlier, earlier, ⟨earlierOpen, earlierQuiet, barriers, input⟩, rfl⟩
  exact ⟨result, candidate, fun other legal => minimal _ (priorityWord_length other) ⟨other, legal, rfl⟩⟩

theorem Canonical.unique_order {input : List (AddressedCommand Name Key Code)} {left right : Trace program last}
    (first : Canonical input left) (second : Canonical input right) :
    ∀ cut, cut < last → addressedEventAt left cut = addressedEventAt right cut := by
  have words := List.le_antisymm (first.2 right second.1) (second.2 left first.1)
  exact addressed_order_of_equal_priority_words left right (first.1.2.2.2.trans second.1.2.2.2.symm) words

/-- Equal addressed orders and equal command words fix the literal
root insertions and permit one consistent redraw between the histories. -/
theorem consistent_redraw_of_addressed_order (left right : Trace program last)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (rightOpen : ¬ Nonempty (ClosedEpisode right))
    (leftQuiet : Progress.Quiet (left.state last)) (rightQuiet : Progress.Quiet (right.state last))
    (stable : GuardedLandingMatching.ChildContinuations program)
    (input : orchestrationInput left = orchestrationInput right)
    (ordered : ∀ cut, cut < last → addressedEventAt left cut = addressedEventAt right cut) :
    GuardedIncarnationRedraw.ConsistentRedraw left right := by
  apply GuardedIncarnationRedraw.consistent_redraw_of_open_events left right stable
    (open_events_of_ordered_addresses left right leftOpen rightOpen leftQuiet rightQuiet ordered)
  intro cut name other component bounded first second
  have command := next_commands_agree left right (span := 0) bounded bounded
    (fun i earlier => ordered i (by omega)) input first second (fun i lower upper => by omega)
  simpa [commandAt, first, second] using command

def insertionName : AddressedCommand Name Key Code → Option Name
  | .insert name _ => some name
  | _ => none

private def insertionAt (trace : Trace program last) (cut : Nat) : Option Name :=
  match trace.event cut with
  | .command (.insert name _) => some name
  | _ => none

private theorem insertionAt_eq (trace : Trace program last) (cut : Nat) :
    (commandAt trace cut).bind insertionName = insertionAt trace cut := by
  cases event : trace.event cut with
  | lifecycle => simp [commandAt, insertionAt, event]
  | command command =>
    cases command with
    | insert => simp [commandAt, insertionAt, insertionName, event]
    | retire name | remove name =>
      cases found : targetAt trace cut name <;> simp [commandAt, insertionAt, insertionName, event, found]

private theorem insertion_count (trace : Trace program last) (cut : Nat) :
    ((List.range cut).filterMap (insertionAt trace)).length = occurrencesBefore (isRootInsertion trace) cut := by
  induction cut with
  | zero => rfl
  | succ cut ih =>
    rw [List.range_succ, List.filterMap_append, List.length_append, ih, occurrencesBefore]
    cases event : trace.event cut with
    | lifecycle => simp [insertionAt, isRootInsertion, event]
    | command command => cases command <;> simp [insertionAt, isRootInsertion, event]

private theorem insertion_name_at_rank (trace : Trace program last) {cut : Nat} (bounded : cut + 1 < last)
    {name : Name} {component : Component Key Code} (insertion : trace.event cut = .command (.insert name component)) :
    ((orchestrationInput trace).filterMap insertionName)[occurrencesBefore (isRootInsertion trace) cut]? = some name := by
  simp only [orchestrationInput, List.filterMap_filterMap, insertionAt_eq]
  rw [cut_range_pair bounded, List.filterMap_append, ← insertion_count trace cut,
    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  simp [insertionAt, insertion]

def decodeRootCommand (insertions : List Name) : AddressedCommand Name Key Code → Option (Command Name Key Code)
  | .insert name component => some (.insert name component)
  | .retire (.root ordinal) _ => insertions[ordinal]?.map .retire
  | .remove (.root ordinal) _ => insertions[ordinal]?.map .remove
  | _ => none

private theorem command_target_origin (trace : Trace program last) {cut : Nat} (bounded : cut < last) {name : Name}
    {path : Address} {component : Component Key Code} (target : targetAt trace cut name = some (path, component)) :
    (∃ rank, rootAt (trace.state cut) name = true ∧ path = .root rank ∧
      ((orchestrationInput trace).filterMap insertionName)[rank]? = some name) ∨
    ∃ parent rank, rootAt (trace.state cut) name = false ∧ path = .child parent rank := by
  obtain ⟨stamp, row, tag, addressed, found, _⟩ := (targetAt_eq_some trace).mp target
  have actual := (GuardedBirthMatching.recorded_birth trace (Nat.le_of_lt bounded) tag).1
  have stamped := tag
  rw [trace.notes_eq cut (Nat.le_of_lt bounded)] at stamped
  have life := Incarnation.resident_of_birthAt stamped
  have parentUnchanged {initial} (atBirth : trace.state stamp name = some initial) :
      initial.parent = row.parent :=
    (life.metadata_of_stable (fun step inside => transition_stable (trace.step step inside).1)
      (Nat.le_of_lt bounded) atBirth found).2
  cases addressed with
  | @root birth insertedName payload inside insertion =>
    have step := (trace.step birth inside).1
    rw [insertion] at step
    have atBirth : trace.state (birth + 1) insertedName = some (fresh payload none) := by
      rw [step.2]
      exact put_self _ _ _
    have inserted : GuardedBirthMatching.BornAt trace insertedName (birth + 1) :=
      ⟨by omega, by omega, step.1.1, by simp [atBirth]⟩
    have same := GuardedBirthMatching.born_unique trace actual inserted
    subst insertedName
    have parent : row.parent = none := (parentUnchanged atBirth).symm
    have bornBefore := life.ordered
    exact .inl ⟨_, by simp [rootAt, found, parent], rfl, insertion_name_at_rank trace (by omega) insertion⟩
  | @child birth parentBirth childName parent inside stage absent present tagAt _ =>
    have childBorn : GuardedBirthMatching.BornAt trace childName (birth + 1) :=
      ⟨by omega, by omega, absent, present⟩
    have same := GuardedBirthMatching.born_unique trace actual childBorn
    subst childName
    obtain ⟨payload, atBirth⟩ := EpisodeBoundary.born_row absent (trace.actual_child_birth inside stage absent present).1
    have ancestry : row.parent = some (trace.actor birth) := (parentUnchanged atBirth).symm
    exact .inr ⟨parent, _, by simp [rootAt, found, ancestry], rfl⟩

/-- The full addressed word determines the literal original root word.
The ordinal in a root address resolves to its original insertion name,
even if that same raw name was used for a different incarnation. -/
theorem originalRoots_of_input (trace : Trace program last) : originalRoots trace =
      (orchestrationInput trace).filterMap (decodeRootCommand ((orchestrationInput trace).filterMap insertionName)) := by
  let decode := decodeRootCommand (Key := Key) (Code := Code) ((orchestrationInput trace).filterMap insertionName)
  have atCut (cut : Nat) (bounded : cut < last) :
      eventRoots (trace.state cut) (trace.event cut) = ((commandAt trace cut).bind decode).toList := by
    cases event : trace.event cut with
    | lifecycle => simp [event, commandAt, eventRoots]
    | command command =>
      cases command with
      | insert => simp [decode, decodeRootCommand, commandAt, event, eventRoots, commandRoots]
      | retire name =>
        obtain ⟨path, component, target⟩ := targetAt_command trace bounded (.inl event)
        rcases command_target_origin trace bounded target with ⟨rank, root, rfl, known⟩ | ⟨parent, rank, child, rfl⟩
        · simp [decode, decodeRootCommand, commandAt, event, eventRoots, commandRoots, target, root, known]
        · simp [decode, decodeRootCommand, commandAt, event, eventRoots, commandRoots, target, child]
      | remove name =>
        obtain ⟨path, component, target⟩ := targetAt_command trace bounded (.inr event)
        rcases command_target_origin trace bounded target with ⟨rank, root, rfl, known⟩ | ⟨parent, rank, child, rfl⟩
        · simp [decode, decodeRootCommand, commandAt, event, eventRoots, commandRoots, target, root, known]
        · simp [decode, decodeRootCommand, commandAt, event, eventRoots, commandRoots, target, child]
  change (List.range last).flatMap _ = ((List.range last).filterMap (commandAt trace)).filterMap decode
  rw [List.filterMap_filterMap]
  have fold (cuts : List Nat) (bounded : ∀ cut ∈ cuts, cut < last) :
      cuts.flatMap (fun cut => eventRoots (trace.state cut) (trace.event cut)) =
        cuts.filterMap (fun cut => (commandAt trace cut).bind decode) := by
    induction cuts with
    | nil => rfl
    | cons cut rest ih =>
      rw [List.flatMap_cons, atCut cut (bounded cut List.mem_cons_self), ih (fun i member => bounded i (List.mem_cons_of_mem _ member))]
      cases command : (commandAt trace cut).bind decode <;> simp [command]
  exact fold _ (fun _ member => List.mem_range.mp member)

theorem same_root_commands {rightLength : Nat} (left : Trace program last) (right : Trace program rightLength)
    (input : orchestrationInput left = orchestrationInput right) : originalRoots left = originalRoots right := by
  rw [originalRoots_of_input left, originalRoots_of_input right, input]

/-- Root-only orchestration excludes explicit commands to child
incarnations. Children may still be allocated and retired by saved words. -/
def RootOnlyInput (input : List (AddressedCommand Name Key Code)) : Prop :=
  ∀ parent stage component,
    .retire (.child parent stage) component ∉ input ∧ .remove (.child parent stage) component ∉ input

/-- A retained child command still targets a child in the original
history. Retention maps the target's actual birth and its source event. -/
theorem retained_root_only_input {length : Nat} {original : Trace program last} {compact : Trace program length}
    {expand : Nat → Nat} (retained : RetainedEvents original compact expand)
    (roots : RootOnlyInput (orchestrationInput original)) :
    RootOnlyInput (orchestrationInput compact) := by
  have childTarget {cut : Nat} (bounded : cut < length) {name : Name} {parent : Address}
      {stage : Nat} {component : Component Key Code}
      (command : compact.event cut = .command (.retire name) ∨ compact.event cut = .command (.remove name))
      (target : targetAt compact cut name = some (.child parent stage, component)) :
      ∃ oldParent oldStage, targetAt original (expand (cut + 1) - 1) name =
        some (.child oldParent oldStage, component) := by
    obtain ⟨birth, newAddress, oldAddress, part, freshAddressed, oldAddressed, freshTarget, oldTarget⟩ :=
      retained_command_target retained bounded command
    obtain ⟨addressEq, payloadEq⟩ := Prod.mk.inj (Option.some.inj (freshTarget.symm.trans target))
    subst newAddress
    subst part
    cases oldAddress with
    | child oldParent oldStage => exact ⟨oldParent, oldStage, oldTarget⟩
    | root rank =>
      cases freshAddressed with
      | @child source parentBirth childName childParent sourceBound creates _ _ _ _ =>
        generalize same : expand (source + 1) = oldBirth at oldAddressed
        cases oldAddressed with
        | root oldBound insertion =>
          have mapped := retained.label source sourceBound
          rw [same, Nat.add_sub_cancel, insertion] at mapped
          simp [Trace.rule, mapped, eventRule, ExchangeReplay.commandRule, EpisodeSelection.canBirth] at creates
  intro parent stage component
  constructor
  · intro member
    obtain ⟨cut, inside, value⟩ := List.mem_filterMap.mp member
    have bounded := List.mem_range.mp inside
    cases event : compact.event cut with
    | lifecycle => simp [commandAt, event] at value
    | command command =>
      cases command with
      | insert => simp [commandAt, event] at value
      | remove name =>
        obtain ⟨_, _, target⟩ := targetAt_command compact bounded (.inr event)
        simp [commandAt, event, target] at value
      | retire name =>
        obtain ⟨path, part, target⟩ := targetAt_command compact bounded (.inl event)
        have same : AddressedCommand.retire (Name := Name) path part = .retire (.child parent stage) component :=
          Option.some.inj (by simpa [commandAt, event, target] using value)
        obtain ⟨rfl, rfl⟩ := AddressedCommand.retire.inj same
        obtain ⟨previousParent, previousStage, previous⟩ := childTarget bounded (.inl event) target
        have originalEvent := (retained.label cut bounded).symm.trans event
        have insideOriginal := retained.stamp cut bounded
        exact (roots previousParent previousStage part).1 (List.mem_filterMap.mpr
          ⟨expand (cut + 1) - 1, List.mem_range.mpr (by omega), by simp [commandAt, originalEvent, previous]⟩)
  · intro member
    obtain ⟨cut, inside, value⟩ := List.mem_filterMap.mp member
    have bounded := List.mem_range.mp inside
    cases event : compact.event cut with
    | lifecycle => simp [commandAt, event] at value
    | command command =>
      cases command with
      | insert => simp [commandAt, event] at value
      | retire name =>
        obtain ⟨_, _, target⟩ := targetAt_command compact bounded (.inl event)
        simp [commandAt, event, target] at value
      | remove name =>
        obtain ⟨path, part, target⟩ := targetAt_command compact bounded (.inr event)
        have same : AddressedCommand.remove (Name := Name) path part = .remove (.child parent stage) component :=
          Option.some.inj (by simpa [commandAt, event, target] using value)
        obtain ⟨rfl, rfl⟩ := AddressedCommand.remove.inj same
        obtain ⟨previousParent, previousStage, previous⟩ := childTarget bounded (.inr event) target
        have originalEvent := (retained.label cut bounded).symm.trans event
        have insideOriginal := retained.stamp cut bounded
        exact (roots previousParent previousStage part).2 (List.mem_filterMap.mpr
          ⟨expand (cut + 1) - 1, List.mem_range.mpr (by omega), by simp [commandAt, originalEvent, previous]⟩)

/-- If all addressed commands target roots, the birth barriers force
every command ahead of the activations. -/
theorem Candidate.commands_first {trace : Trace program last} {input : List (AddressedCommand Name Key Code)}
    (candidate : Candidate input trace)
    (roots : RootOnlyInput input) :
    ∃ split, split ≤ last ∧
      (∀ cut, cut < split → ∃ command, trace.event cut = .command command) ∧
      (∀ cut, split ≤ cut → cut < last → ∃ kind actor, trace.event cut = .lifecycle kind actor) := by
  have noLateCommand {cut : Nat} (bounded : cut + 1 < last) {kind actor command}
      (activation : trace.event cut = .lifecycle kind actor)
      (external : trace.event (cut + 1) = .command command) : False := by
    obtain ⟨absent, present⟩ := candidate.2.2.1 cut bounded kind actor command activation external
    have noRoot {name : Name} (vacant : trace.state cut name = none)
        {rank component} (found : targetAt trace (cut + 1) name = some (.root rank, component)) : False := by
      obtain ⟨birth, _, tag, path, _, _⟩ := (targetAt_eq_some trace).mp found
      rw [trace.notes_eq _ (by omega)] at tag
      have resident := Incarnation.resident_of_birthAt tag
      have exactBirth : birth = cut + 1 := by
        have := resident.ordered
        have after : cut < birth := Nat.lt_of_not_ge fun earlier =>
          resident.present cut earlier (by omega) vacant
        omega
      rw [exactBirth] at path
      cases path with
      | root _ inserted => rw [activation] at inserted; cases inserted
    cases command with
    | insert name component =>
      have step := (trace.step (cut + 1) bounded).1
      rw [external] at step
      exact present step.1.1
    | retire name =>
      obtain ⟨path, component, target⟩ := targetAt_command trace bounded (.inl external)
      cases path with
      | root => exact noRoot absent target
      | child parent stage =>
        apply (roots parent stage component).1
        rw [← candidate.2.2.2]
        exact List.mem_filterMap.mpr ⟨cut + 1, List.mem_range.mpr bounded, by simp [commandAt, external, target]⟩
    | remove name =>
      obtain ⟨path, component, target⟩ := targetAt_command trace bounded (.inr external)
      cases path with
      | root => exact noRoot absent target
      | child parent stage =>
        apply (roots parent stage component).2
        rw [← candidate.2.2.2]
        exact List.mem_filterMap.mpr ⟨cut + 1, List.mem_range.mpr bounded, by simp [commandAt, external, target]⟩
  have shape (length : Nat) (bounded : length ≤ last) : ∃ split, split ≤ length ∧
      (∀ cut, cut < split → ∃ command, trace.event cut = .command command) ∧
      (∀ cut, split ≤ cut → cut < length → ∃ kind actor, trace.event cut = .lifecycle kind actor) := by
    induction length with
    | zero => exact ⟨0, Nat.le_refl _, fun _ impossible => False.elim (by omega), fun _ _ impossible => False.elim (by omega)⟩
    | succ length ih =>
      obtain ⟨split, within, commands, activations⟩ := ih (by omega)
      cases event : trace.event length with
      | lifecycle kind actor =>
        refine ⟨split, by omega, commands, fun cut lower upper => ?_⟩
        by_cases same : cut = length
        · exact ⟨kind, actor, same.symm ▸ event⟩
        · exact activations cut lower (by omega)
      | command command =>
        have equal : split = length := by
          apply Classical.byContradiction
          intro different
          obtain ⟨kind, actor, previous⟩ := activations (length - 1) (by omega) (by omega)
          have atLength : length - 1 + 1 = length := by omega
          exact noLateCommand (by omega) previous (atLength.symm ▸ event)
        refine ⟨length + 1, Nat.le_refl _, fun cut inside => ?_, fun _ _ impossible => False.elim (by omega)⟩
        by_cases same : cut = length
        · exact ⟨command, same.symm ▸ event⟩
        · exact commands cut (by omega)
  exact shape last (Nat.le_refl _)

private theorem roots_at_root_command (trace : Trace program last)
    (roots : RootOnlyInput (orchestrationInput trace))
    {cut : Nat} (bounded : cut < last) {command : Command Name Key Code}
    (event : trace.event cut = .command command) :
    eventRoots (trace.state cut) (trace.event cut) = [command] := by
  cases command with
  | insert => simp [event, eventRoots, commandRoots]
  | retire name =>
    obtain ⟨path, component, target⟩ := targetAt_command trace bounded (.inl event)
    rcases command_target_origin trace bounded target with ⟨_, root, _, _⟩ | ⟨parent, stage, _, rfl⟩
    · simp [event, eventRoots, commandRoots, root]
    · exact False.elim ((roots parent stage component).1
        (List.mem_filterMap.mpr ⟨cut, List.mem_range.mpr bounded, by simp [commandAt, event, target]⟩))
  | remove name =>
    obtain ⟨path, component, target⟩ := targetAt_command trace bounded (.inr event)
    rcases command_target_origin trace bounded target with ⟨_, root, _, _⟩ | ⟨parent, stage, _, rfl⟩
    · simp [event, eventRoots, commandRoots, root]
    · exact False.elim ((roots parent stage component).2
        (List.mem_filterMap.mpr ⟨cut, List.mem_range.mpr bounded, by simp [commandAt, event, target]⟩))

/-- Root-only orchestration can be checked directly against the parent
fields of the actual rows targeted at each command cut. -/
theorem root_only_input_iff_root_targets (trace : Trace program last) :
    RootOnlyInput (orchestrationInput trace) ↔
      ∀ cut, cut < last → ∀ name,
        (trace.event cut = .command (.retire name) ∨ trace.event cut = .command (.remove name)) →
        rootAt (trace.state cut) name = true := by
  constructor
  · intro roots cut bounded name command
    rcases command with retire | remove
    · have singleton := roots_at_root_command trace roots bounded retire
      cases flag : rootAt (trace.state cut) name <;> simp_all [eventRoots, commandRoots]
    · have singleton := roots_at_root_command trace roots bounded remove
      cases flag : rootAt (trace.state cut) name <;> simp_all [eventRoots, commandRoots]
  · intro rootTargets parent stage component
    constructor <;> intro member <;>
      obtain ⟨cut, inside, selected⟩ := List.mem_filterMap.mp member <;>
      have bounded := List.mem_range.mp inside <;>
      cases event : trace.event cut with
      | lifecycle => simp [commandAt, event] at selected
      | command command =>
        cases command with
        | insert => simp [commandAt, event] at selected
        | retire name | remove name =>
          have external : trace.event cut = .command (.retire name) ∨
              trace.event cut = .command (.remove name) := by simp [event]
          obtain ⟨path, payload, target⟩ := targetAt_command trace bounded external
          have root := rootTargets cut bounded name external
          rcases command_target_origin trace bounded target with ⟨rank, _, rfl, _⟩ | ⟨_, _, child, _⟩
          · simp [commandAt, event, target] at selected
          · simp [root] at child

private theorem command_block_words (trace : Trace program last)
    (roots : RootOnlyInput (orchestrationInput trace)) {split : Nat} (bounded : split ≤ last)
    (commands : ∀ cut, cut < split → ∃ command, trace.event cut = .command command)
    (activations : ∀ cut, split ≤ cut → cut < last → ∃ kind actor, trace.event cut = .lifecycle kind actor) :
    ∃ word : Nat → Command Name Key Code,
      originalRoots trace = (List.range split).map word ∧
      (∀ cut, cut < split → trace.event cut = .command (word cut)) ∧
      orchestrationInput trace = (List.range split).filterMap (commandAt trace) := by
  classical
  let word (cut : Nat) : Command Name Key Code :=
    if earlier : cut < split then Classical.choose (commands cut earlier) else .remove (trace.actor cut)
  have label (cut : Nat) (earlier : cut < split) : trace.event cut = .command (word cut) := by
    simpa only [word, dif_pos earlier] using Classical.choose_spec (commands cut earlier)
  have range : List.range last = List.range split ++ (List.range (last - split)).map (split + ·) := by
    have same : split + (last - split) = last := by omega
    simpa only [same] using (List.range_add (n := split) (m := last - split))
  have late (cut : Nat) (member : cut ∈ (List.range (last - split)).map (split + ·)) :
      ∃ kind actor, trace.event cut = .lifecycle kind actor := by
    obtain ⟨i, inside, rfl⟩ := List.mem_map.mp member
    have lower := List.mem_range.mp inside
    exact activations _ (by omega) (by omega)
  refine ⟨word, ?_, label, ?_⟩
  · unfold originalRoots
    rw [range, List.flatMap_append]
    have empty : ((List.range (last - split)).map (split + ·)).flatMap
        (fun cut => eventRoots (trace.state cut) (trace.event cut)) = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro cut member
      obtain ⟨kind, actor, event⟩ := late cut member
      simp [event, eventRoots]
    rw [empty, List.append_nil, List.map_eq_flatMap]
    simp only [List.flatMap_def]
    congr 1
    apply List.map_congr_left
    intro cut member
    have earlier := List.mem_range.mp member
    exact roots_at_root_command trace roots (by omega) (label cut earlier)
  · unfold orchestrationInput
    rw [range, List.filterMap_append]
    have empty : ((List.range (last - split)).map (split + ·)).filterMap (commandAt trace) = [] := by
      apply List.filterMap_eq_nil_iff.mpr
      intro cut member
      obtain ⟨kind, actor, event⟩ := late cut member
      simp [commandAt, event]
    simp [empty]

/-- Quiet, open histories with only root commands are determined at the
level of addressed input by the literal root word, even with reused names. -/
theorem root_only_input_of_same_roots {rightLength : Nat}
    (left : Trace program last) (right : Trace program rightLength)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (leftQuiet : Progress.Quiet (left.state last))
    (rightOpen : ¬ Nonempty (ClosedEpisode right)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (leftRoots : RootOnlyInput (orchestrationInput left)) (rightRoots : RootOnlyInput (orchestrationInput right))
    (same : originalRoots left = originalRoots right) :
    orchestrationInput left = orchestrationInput right := by
  obtain ⟨first, _, firstBarriers, _, firstInput, firstRoots, _, firstOpen, firstQuiet⟩ :=
    push_commands_to_birth_barriers left leftOpen leftQuiet
  obtain ⟨second, _, secondBarriers, _, secondInput, secondRoots, _, secondOpen, secondQuiet⟩ :=
    push_commands_to_birth_barriers right rightOpen rightQuiet
  have leftRootOnly : RootOnlyInput (orchestrationInput first) := firstInput.symm ▸ leftRoots
  have rightRootOnly : RootOnlyInput (orchestrationInput second) := secondInput.symm ▸ rightRoots
  obtain ⟨n, within, commands, activations⟩ :=
    Candidate.commands_first (trace := first) ⟨firstOpen, firstQuiet, firstBarriers, rfl⟩ leftRootOnly
  obtain ⟨m, withinRight, rightCommands, rightActivations⟩ :=
    Candidate.commands_first (trace := second) ⟨secondOpen, secondQuiet, secondBarriers, rfl⟩ rightRootOnly
  obtain ⟨firstWord, leftWord, firstLabels, leftInput⟩ :=
    command_block_words first leftRootOnly within commands activations
  obtain ⟨secondWord, rightWord, secondLabels, rightInput⟩ :=
    command_block_words second rightRootOnly withinRight rightCommands rightActivations
  have words := leftWord.symm.trans (firstRoots.trans (same.trans (secondRoots.symm.trans rightWord)))
  have lengthEq : n = m := by simpa using congrArg List.length words
  subst m
  have events (cut : Nat) (inside : cut < n) : first.event cut = second.event cut := by
    have nth := congrArg (fun word : List (Command Name Key Code) => word[cut]?) words
    have member : (List.range n)[cut]? = some cut := by simp [inside]
    have commandEq : firstWord cut = secondWord cut := by simpa [List.getElem?_map, member] using nth
    rw [firstLabels cut inside, secondLabels cut inside, commandEq]
  have cuts (cut : Nat) (bounded : cut ≤ n) :
      first.state cut = second.state cut ∧ first.notes cut = second.notes cut := by
    induction cut with
    | zero => exact ⟨first.start.trans second.start.symm, first.seed.trans second.seed.symm⟩
    | succ cut ih =>
      obtain ⟨sameState, sameNotes⟩ := ih (by omega)
      obtain ⟨command, atFirst⟩ := commands cut (by omega)
      have atSecond := (events cut (by omega)).symm.trans atFirst
      have firstStep := first.step cut (by omega)
      have secondStep := second.step cut (by omega)
      have leftStep := firstStep.1
      have rightStep := secondStep.1
      rw [atFirst] at leftStep
      rw [atSecond] at rightStep
      have nextState := leftStep.2.trans ((congrArg command.apply sameState).trans rightStep.2.symm)
      exact ⟨nextState, by rw [firstStep.2, secondStep.2, sameState, nextState, sameNotes, events cut (by omega)]⟩
  have address (birth : Nat) (bounded : birth ≤ n) : addressOf first birth = addressOf second birth := by
    cases before : addressOf first birth with
    | none =>
      cases after : addressOf second birth with
      | none => rfl
      | some path =>
        have moved := ((addressOf_eq_some second).mp after).transport_prefix within
          (fun i valid => (events i valid).symm)
          (fun i valid name => by rw [(cuts i valid).1])
          (fun i valid => congrArg Prod.fst (cuts i valid).2.symm) bounded
        exact False.elim (Option.noConfusion (before.symm.trans ((addressOf_eq_some first).mpr moved)))
    | some path =>
      have moved := ((addressOf_eq_some first).mp before).transport_prefix withinRight events
        (fun i valid name => by rw [(cuts i valid).1])
        (fun i valid => congrArg Prod.fst (cuts i valid).2) bounded
      exact ((addressOf_eq_some second).mpr moved).symm
  have inputAt (cut : Nat) (bounded : cut < n) : commandAt first cut = commandAt second cut := by
    have target (name : Name) : targetAt first cut name = targetAt second cut name := by
      have equal := cuts cut (by omega)
      unfold targetAt
      rw [equal.1, equal.2]
      cases known : (second.notes cut).1 name with
      | none => rfl
      | some birth =>
        have earlier := (GuardedBirthMatching.recorded_birth second (by omega : cut ≤ rightLength) known).2
        simp [address birth (by omega)]
    unfold commandAt
    rw [events cut bounded]
    cases second.event cut with
    | lifecycle => rfl
    | command command => cases command <;> simp only [target]
  rw [← firstInput, ← secondInput, leftInput, rightInput]
  change (List.range n).filterMap (id ∘ commandAt first) =
    (List.range n).filterMap (id ∘ commandAt second)
  rw [← List.filterMap_map, ← List.filterMap_map]
  congr 1
  apply List.map_congr_left
  intro cut member
  exact inputAt cut (List.mem_range.mp member)

section Typed
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PaperObservationEquations (OperationRespects)
open PartialCoeffectIndependenceContracts (tableSetoid)
open GuardedLandingMatching (ChildContinuations)
open GuardedCutState (ProjectedAgreement)
open GuardedScheduleMatching (CutAgreement match_open_prefix)
open TypedRegistry (Scalar encodeProgram)

variable {V : Key → Type u} {ops : CoeffectOperations V}
variable {typedProgram : Code → TypedRegistry.Instruction Name ops Code}

/-- An addressed order identifies a single exchange class, even when
two concrete schedules chose different names for their child births. -/
theorem schedule_path_of_addressed_order [Setoid (Scalar ops)]
    (left right : Trace (encodeProgram typedProgram) last)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (rightOpen : ¬ Nonempty (ClosedEpisode right))
    (leftQuiet : Progress.Quiet (left.state last)) (rightQuiet : Progress.Quiet (right.state last))
    (stable : ChildContinuations (encodeProgram typedProgram))
    (input : orchestrationInput left = orchestrationInput right)
    (ordered : ∀ cut, cut < last → addressedEventAt left cut = addressedEventAt right cut) :
    GuardedCompleteAlignment.ScheduleAlignmentPath left right := by
  have cuts := match_open_prefix left right stable last (Nat.le_refl _) (Nat.le_refl _)
    (open_events_of_ordered_addresses left right leftOpen rightOpen leftQuiet rightQuiet ordered)
  exact .redraw cuts input.symm
    (addressedEvents_congr right left (fun cut bounded => (ordered cut bounded).symm))
    (consistent_redraw_of_addressed_order left right leftOpen rightOpen leftQuiet rightQuiet stable input ordered)

/-- Local redraw availability connects the two actual schedules with a
common command word, including their precise choices of raw names. -/
theorem schedule_path_of_common_input_with_local_redraw
    (left right : Trace (encodeProgram typedProgram) last)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (rightOpen : ¬ Nonempty (ClosedEpisode right))
    (leftQuiet : Progress.Quiet (left.state last)) (rightQuiet : Progress.Quiet (right.state last))
    (stable : ChildContinuations (encodeProgram typedProgram))
    (input : orchestrationInput left = orchestrationInput right)
    (redraw : ∀ source : Trace (encodeProgram typedProgram) last,
      orchestrationInput source = orchestrationInput left →
      (addressedEvents source).Perm (addressedEvents right) →
      GuardedIncarnationRedraw.LiveDomainRenaming (right.state last) (source.state last) →
      GuardedCompleteAlignment.RedrawAtReuseFor source)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    GuardedCompleteAlignment.ScheduleAlignmentPath right left := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  obtain ⟨moved, _, _, ordered, commands, _, movedOpen, movedQuiet, _, path⟩ :=
    GuardedCompleteAlignment.align_surviving_schedules_with_local_redraw left right leftOpen leftQuiet
      rightOpen rightQuiet stable input redraw observe recovery commutative respect
  have rename := schedule_path_of_addressed_order moved left movedOpen leftOpen movedQuiet leftQuiet
    stable (commands.trans input.symm) (fun cut bounded => (ordered cut bounded).symm)
  exact .trans path rename

/-- An adjacent exchange which puts the lower-priority event first
strictly decreases the canonical word. The comparison follows the
actual actor addresses across the exchange. -/
theorem priorityWord_lt_of_adjacent_exchange [Setoid (Scalar ops)]
    {before after : Trace (encodeProgram typedProgram) last} {cut : Nat}
    (exchange : GuardedActivationAlignment.AdjacentActivationExchange before after cut)
    (earlier : (priorityWord before)[cut + 1]?.getD 0 < (priorityWord before)[cut]?.getD 0) :
    priorityWord after < priorityWord before := by
  have bounded := exchange.bounded
  have first : cut < last := by omega
  have next : addressedEventAt after cut = addressedEventAt before (cut + 1) := by
    simpa only [ExchangeReplay.exchangedIndex_first, Nat.add_sub_cancel] using
      stable_addressed_event exchange.addresses first
  have prior : (List.range cut).map (fun i => eventRank (addressedEventAt after i)) =
      (List.range cut).map (fun i => eventRank (addressedEventAt before i)) := by
    apply List.map_congr_left
    intro i member
    have inside := List.mem_range.mp member
    have atCut := stable_addressed_event exchange.addresses (cut := i) (by omega)
    rw [ExchangeReplay.exchangedIndex_other (by omega) (by omega), Nat.add_sub_cancel] at atCut
    exact congrArg eventRank atCut
  have order : eventRank (addressedEventAt after cut) < eventRank (addressedEventAt before cut) := by
    rw [next]
    simpa [priorityWord, List.getElem?_map, List.getElem?_range, first, bounded] using earlier
  unfold priorityWord
  rw [cut_range_pair bounded, List.map_append, List.map_append, prior]
  simp only [List.map_cons]
  generalize (List.range cut).map (fun i => eventRank (addressedEventAt before i)) = initial
  induction initial with
  | nil => exact .rel order
  | cons _ _ ih => exact .cons ih

/-- Minimize over legal candidates reachable by certified exchanges and
redraws inside the original name set. The command exchanges provide an
initial candidate even when no fresh name can be reserved for alignment. -/
theorem exists_least_reachable_schedule [Setoid (Scalar ops)]
    (source : Trace (encodeProgram typedProgram) last)
    (opened : ¬ Nonempty (ClosedEpisode source)) (quiet : Progress.Quiet (source.state last)) :
    ∃ result : Trace (encodeProgram typedProgram) last,
      Candidate (orchestrationInput source) result ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath source result ∧
      ∀ other : Trace (encodeProgram typedProgram) last, Candidate (orchestrationInput source) other →
        GuardedCompleteAlignment.ScheduleAlignmentPath source other → priorityWord result ≤ priorityWord other := by
  obtain ⟨earlier, _, barriers, _, input, _, _, earlierOpen, earlierQuiet, commandPath⟩ :=
    push_commands_to_birth_barriers_with_path source opened quiet
  let realizes (word : List Nat) :=
    ∃ result : Trace (encodeProgram typedProgram) last,
      Candidate (orchestrationInput source) result ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath source result ∧ priorityWord result = word
  obtain ⟨least, _, ⟨result, candidate, path, rfl⟩, minimal⟩ := least_priority_word last realizes
    ⟨_, priorityWord_length earlier, earlier, ⟨earlierOpen, earlierQuiet, barriers, input⟩,
      .command commandPath, rfl⟩
  exact ⟨result, candidate, path, fun other legal reachable =>
    minimal _ (priorityWord_length other) ⟨other, legal, reachable, rfl⟩⟩

/-- Starting at either end of a certified path gives the same reachable
candidates and priority minimum. -/
theorem reachable_candidates_iff [Setoid (Scalar ops)]
    {first second candidate : Trace (encodeProgram typedProgram) last}
    (between : GuardedCompleteAlignment.ScheduleAlignmentPath first second) :
    (Candidate (orchestrationInput first) candidate ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath first candidate) ↔
    (Candidate (orchestrationInput second) candidate ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath second candidate) := by
  rw [between.input_eq]
  exact and_congr_right fun _ => ⟨fun path => .trans (.reverse between) path,
    fun path => .trans between path⟩

/-- At a least reachable schedule, every certified adjacent exchange
that remains a candidate respects the order of the two events. -/
theorem least_reachable_adjacent_order [Setoid (Scalar ops)]
    {source least after : Trace (encodeProgram typedProgram) last} {cut : Nat}
    (path : GuardedCompleteAlignment.ScheduleAlignmentPath source least)
    (minimal : ∀ other : Trace (encodeProgram typedProgram) last, Candidate (orchestrationInput source) other →
      GuardedCompleteAlignment.ScheduleAlignmentPath source other → priorityWord least ≤ priorityWord other)
    (exchange : GuardedActivationAlignment.AdjacentActivationExchange least after cut)
    (candidate : Candidate (orchestrationInput source) after) :
    (priorityWord least)[cut]?.getD 0 ≤ (priorityWord least)[cut + 1]?.getD 0 := by
  apply Nat.le_of_not_gt
  intro inversion
  exact (List.not_le.mpr (priorityWord_lt_of_adjacent_exchange exchange inversion))
    (minimal after candidate (.trans path (.swap exchange)))

/-- The reachable minimum has the global canonical word exactly when a
global canonical schedule is reachable by the certified moves. -/
theorem least_reachable_word_eq_iff [Setoid (Scalar ops)]
    {source least canonical : Trace (encodeProgram typedProgram) last}
    (legal : Candidate (orchestrationInput source) least)
    (path : GuardedCompleteAlignment.ScheduleAlignmentPath source least)
    (minimal : ∀ other : Trace (encodeProgram typedProgram) last, Candidate (orchestrationInput source) other →
      GuardedCompleteAlignment.ScheduleAlignmentPath source other → priorityWord least ≤ priorityWord other)
    (global : Canonical (orchestrationInput source) canonical) :
    priorityWord least = priorityWord canonical ↔
      ∃ result : Trace (encodeProgram typedProgram) last, Canonical (orchestrationInput source) result ∧
        GuardedCompleteAlignment.ScheduleAlignmentPath source result := by
  constructor
  · intro same
    exact ⟨least, ⟨legal, fun other candidate => same.symm ▸ global.2 other candidate⟩, path⟩
  · rintro ⟨result, form, reachable⟩
    have equal : priorityWord result = priorityWord canonical :=
      List.le_antisymm (form.2 canonical global.1) (global.2 result form.1)
    exact List.le_antisymm (equal ▸ minimal result form.1 reachable) (global.2 least legal)

/-- Reaching any canonical witness suffices to reach every concrete
realization of its canonical order. -/
theorem Canonical.reachable_iff [Setoid (Scalar ops)]
    {source left right : Trace (encodeProgram typedProgram) last}
    {input : List (AddressedCommand Name Key Code)}
    (first : Canonical input left) (second : Canonical input right)
    (stable : ChildContinuations (encodeProgram typedProgram)) :
    GuardedCompleteAlignment.ScheduleAlignmentPath source left ↔
      GuardedCompleteAlignment.ScheduleAlignmentPath source right := by
  have redraw := schedule_path_of_addressed_order left right first.1.1 second.1.1
    first.1.2.1 second.1.2.1 stable (first.1.2.2.2.trans second.1.2.2.2.symm)
    (first.unique_order second)
  exact ⟨fun path => .trans path redraw, fun path => .trans path (.reverse redraw)⟩

/-- Canonical survivors of the same length and input have matching cuts
in the original name set. -/
theorem Canonical.compare_at_common_length {input : List (AddressedCommand Name Key Code)}
    {left right : Trace (encodeProgram typedProgram) last}
    (first : Canonical input left) (second : Canonical input right)
    (stable : ChildContinuations (encodeProgram typedProgram)) :
    ∀ cut, cut ≤ last → CutAgreement left right cut := by
  intro cut bounded
  apply match_open_prefix left right stable cut bounded bounded
  intro i before
  exact open_events_of_ordered_addresses left right first.1.1 second.1.1 first.1.2.1 second.1.2.1
    (first.unique_order second) i (by omega)

/-- The actual saved words of equal-length canonical survivors agree at
every replay prefix under the partial binding semantics. -/
theorem Canonical.compare_saved_replays {input : List (AddressedCommand Name Key Code)}
    {left right : Trace (encodeProgram typedProgram) last}
    (first : Canonical input left) (second : Canonical input right)
    (stable : ChildContinuations (encodeProgram typedProgram))
    (meaning : PartialReplayRegistry.Coeffects (encodeProgram typedProgram))
    (cut : Nat) (bounded : cut ≤ last) :
    letI : Setoid (Scalar ops) := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
    ∃ names : Renaming.Permutation Name,
      Renaming.registry names (GuardedCutState.project (left.state cut)) = GuardedCutState.project (right.state cut) ∧
      ∀ actor,
        ReplayBindingDomains.WordDefined meaning (left.notes cut).1 ((left.notes cut).2 actor) (left.state cut) ∧
        ReplayBindingDomains.WordDefined meaning (right.notes cut).1 ((right.notes cut).2 (names.toFun actor))
          (right.state cut) ∧
        ∀ count, StageSimulation.Related Eq
          (Renaming.registry names (GuardedCutState.project (IncarnationReplay.replay (left.notes cut).1
            (((left.notes cut).2 actor).take count) (left.state cut))))
          (GuardedCutState.project (IncarnationReplay.replay (right.notes cut).1
            (((right.notes cut).2 (names.toFun actor)).take count) (right.state cut))) :=
  GuardedScheduleMatching.CutAgreement.replay_prefixes_in_domain bounded bounded meaning
    (first.compare_at_common_length second stable cut bounded)

/-- Two original endpoints agree if their canonical survivors have the
same length and addressed input and each survivor agrees with its own
source endpoint. -/
theorem Canonical.compare_original_endpoints {input : List (AddressedCommand Name Key Code)}
    {left right : Trace (encodeProgram typedProgram) last} {leftSource rightSource}
    (first : Canonical input left) (second : Canonical input right)
    (stable : ChildContinuations (encodeProgram typedProgram)) (observe : ∀ key, Setoid (V key))
    (leftAgreement : GuardedConfluence.EndpointAgreement observe leftSource (left.state last))
    (rightAgreement : GuardedConfluence.EndpointAgreement observe rightSource (right.state last)) :
    GuardedConfluence.EndpointAgreement observe leftSource rightSource := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  obtain ⟨names, same, _, _⟩ := first.compare_at_common_length second stable last (Nat.le_refl _)
  obtain ⟨names, related⟩ := ProjectedAgreement.of_rename_eq (p := names) same
  have canonicalAgreement : GuardedConfluence.EndpointAgreement observe (left.state last) (right.state last) :=
    ⟨names, _, _, .refl _, .refl _, related⟩
  exact leftAgreement.trans observe (canonicalAgreement.trans observe (rightAgreement.symm observe))

/-- The length and addressed order of canonical surviving schedules depend
only on the surviving command input for the fixed program and name set. -/
theorem Canonical.compare {leftLength rightLength : Nat}
    {input : List (AddressedCommand Name Key Code)}
    {left : Trace (encodeProgram typedProgram) leftLength} {right : Trace (encodeProgram typedProgram) rightLength}
    (first : Canonical input left) (second : Canonical input right)
    (stable : ChildContinuations (encodeProgram typedProgram))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    leftLength = rightLength ∧ (∀ cut, cut < leftLength → addressedEventAt left cut = addressedEventAt right cut) ∧
      ProjectedAgreement (left.state leftLength) (right.state rightLength) ∧
      (∀ cut, cut ≤ leftLength → CutAgreement left right cut) := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  obtain ⟨rfl, _, _⟩ := GuardedNameExtension.compare_open_endpoints left right first.1.1 first.1.2.1
    second.1.1 second.1.2.1 stable (first.1.2.2.2.trans second.1.2.2.2.symm) observe recovery commutative respect
  have cuts := first.compare_at_common_length second stable
  obtain ⟨_, endpoint, _, _⟩ := cuts leftLength (Nat.le_refl _)
  exact ⟨rfl, first.unique_order second, .of_rename_eq endpoint, cuts⟩

private theorem canonical_of_matched_order
    {reference moved : Trace (encodeProgram typedProgram) last}
    {input : List (AddressedCommand Name Key Code)} (canonical : Canonical input reference)
    (opened : ¬ Nonempty (ClosedEpisode moved)) (quiet : Progress.Quiet (moved.state last))
    (sameInput : orchestrationInput moved = input)
    (order : ∀ cut, cut < last → addressedEventAt reference cut = addressedEventAt moved cut) :
    Canonical input moved := by
  have eventsMatch (cut : Nat) (bounded : cut < last) :=
    open_events_of_ordered_addresses reference moved canonical.1.1 opened canonical.1.2.1 quiet order cut bounded
  have barrier : CommandsAtBirthBarriers moved := by
    intro cut bounded kind actor command earlier later
    have pair := eventsMatch cut (by omega)
    cases first : reference.event cut with
    | command cmd => simp [GuardedScheduleMatching.OpenEventsAgree, first, earlier] at pair
    | lifecycle refKind refActor =>
      have atCommand := eventsMatch (cut + 1) bounded
      cases second : reference.event (cut + 1) with
      | lifecycle => simp [GuardedScheduleMatching.OpenEventsAgree, second, later] at atCommand
      | command refCommand =>
        have blocked := canonical.1.2.2.1 cut bounded refKind refActor refCommand first second
        have transfer {old new : Name} (absent : reference.state cut old = none)
            (target : ∃ address component, targetAt reference (cut + 1) old = some (address, component))
            (tags : (reference.notes (cut + 1)).1 old = (moved.notes (cut + 1)).1 new) :
            moved.state cut new = none ∧ moved.state (cut + 1) new ≠ none := by
          obtain ⟨address, component, found⟩ := target
          obtain ⟨birth, _, tag, _, _, _⟩ := (targetAt_eq_some reference).mp found
          have historical := tag
          rw [reference.notes_eq _ (by omega)] at historical
          have resident := Incarnation.resident_of_birthAt historical
          have exactBirth : birth = cut + 1 := by
            have := resident.ordered
            have laterBirth : cut < birth := Nat.lt_of_not_ge fun before =>
              resident.present cut before (by omega) absent
            omega
          have movedTag := tags.symm.trans tag
          have born := (GuardedBirthMatching.recorded_birth moved (by omega) movedTag).1
          simpa [exactBirth] using And.intro born.2.2.1 born.2.2.2
        cases refCommand <;> cases command <;>
          simp [GuardedScheduleMatching.OpenEventsAgree, second, later] at atCommand
        · have insert := (reference.step (cut + 1) bounded).1
          rw [second] at insert
          exact False.elim (blocked.2 insert.1.1)
        · exact transfer blocked.1 (targetAt_command reference bounded (.inl second)) atCommand
        · exact transfer blocked.1 (targetAt_command reference bounded (.inr second)) atCommand
  have word : priorityWord moved = priorityWord reference := by
    unfold priorityWord
    apply List.map_congr_left
    intro cut member
    rw [order cut (List.mem_range.mp member)]
  exact ⟨⟨opened, quiet, barrier, sameInput⟩, fun other legal => word.symm ▸ canonical.2 other legal⟩

/-- Realize the canonical addressed order by a checked alignment path
inside the original name set, provided the needed local redraws exist. -/
theorem align_to_canonical_schedule (trace : Trace (encodeProgram typedProgram) last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    (stable : ChildContinuations (encodeProgram typedProgram))
    (redraw : ∀ source : Trace (encodeProgram typedProgram) last,
      orchestrationInput source = orchestrationInput trace →
      (addressedEvents source).Perm (addressedEvents trace) →
      GuardedIncarnationRedraw.LiveDomainRenaming (trace.state last) (source.state last) →
      GuardedCompleteAlignment.RedrawAtReuseFor source)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ canonical moved : Trace (encodeProgram typedProgram) last,
      Canonical (orchestrationInput trace) canonical ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath trace moved ∧
      (∀ cut, cut < last → addressedEventAt canonical cut = addressedEventAt moved cut) ∧
      originalRoots moved = originalRoots trace ∧
      ProjectedAgreement (trace.state last) (moved.state last) ∧
      (¬ Nonempty (ClosedEpisode moved)) ∧ Progress.Quiet (moved.state last) ∧
      orchestrationInput moved = orchestrationInput trace ∧ Canonical (orchestrationInput trace) moved := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  obtain ⟨canonical, minimal⟩ := exists_canonical trace opened quiet
  obtain ⟨moved, _, _, order, input, endpoint, movedOpen, movedQuiet, _, path⟩ :=
    GuardedCompleteAlignment.align_surviving_schedules_with_local_redraw canonical trace
      minimal.1.1 minimal.1.2.1 opened quiet stable minimal.1.2.2.2 (fun source same events domain => redraw source (same.trans minimal.1.2.2.2) events domain) observe recovery commutative respect
  exact ⟨canonical, moved, minimal, path, order,
    same_root_commands moved trace input, endpoint, movedOpen, movedQuiet, input,
    canonical_of_matched_order minimal movedOpen movedQuiet input order⟩

/-- Without removal commands, even interleaved child retirements admit an
exchange path to the canonical schedule in the original name set. -/
theorem align_to_canonical_without_removals (trace : Trace (encodeProgram typedProgram) last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    (stable : ChildContinuations (encodeProgram typedProgram))
    (noRemovals : ∀ address component, .remove address component ∉ orchestrationInput trace)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ moved : Trace (encodeProgram typedProgram) last,
      Canonical (orchestrationInput trace) moved ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath trace moved ∧
      originalRoots moved = originalRoots trace ∧ ProjectedAgreement (trace.state last) (moved.state last) := by
  obtain ⟨_, moved, _, path, _, roots, endpoint, _, _, _, canonical⟩ :=
    align_to_canonical_schedule trace opened quiet stable
      (fun source same _ _ => GuardedCompleteAlignment.redrawAtReuse_of_no_removals _ noRemovals source same) observe recovery commutative respect
  exact ⟨moved, canonical, path, roots, endpoint⟩

/-- Root-only input admits a certified exchange path to a canonical
survivor in the original name set. -/
theorem align_root_commands_to_canonical (trace : Trace (encodeProgram typedProgram) last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    (stable : ChildContinuations (encodeProgram typedProgram))
    (roots : RootOnlyInput (orchestrationInput trace))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ moved : Trace (encodeProgram typedProgram) last,
      Canonical (orchestrationInput trace) moved ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath trace moved ∧
      originalRoots moved = originalRoots trace ∧ ProjectedAgreement (trace.state last) (moved.state last) := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  obtain ⟨reference, minimal⟩ := exists_canonical trace opened quiet
  obtain ⟨split, bounded, commands, activations⟩ := minimal.1.commands_first roots
  obtain ⟨moved, _, _, _, order, _, input, endpoint, movedOpen, movedQuiet,
      middle, _, _, commandPath, activationPath, _⟩ :=
    GuardedActivationAlignment.align_commands_first reference trace bounded minimal.1.1 minimal.1.2.1
      opened quiet stable minimal.1.2.2.2 commands activations observe recovery commutative respect
  have commandEndpoint := commandPath.preserves.1
  exact ⟨moved, canonical_of_matched_order minimal movedOpen movedQuiet input order,
    .trans (.command commandPath) (.activation activationPath (commandEndpoint.symm ▸ endpoint)),
    same_root_commands moved trace input, .of_related endpoint⟩

/-- Every quiet open history reaches the global canonical schedule
by a certified path within its original name set. -/
theorem canonical_path_in_original_names (trace : Trace (encodeProgram typedProgram) last)
    (opened : ¬ Nonempty (ClosedEpisode trace)) (quiet : Progress.Quiet (trace.state last))
    (stable : ChildContinuations (encodeProgram typedProgram))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ result : Trace (encodeProgram typedProgram) last,
      Canonical (orchestrationInput trace) result ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath trace result := by
  obtain ⟨result, canonical⟩ := exists_canonical trace opened quiet
  exact ⟨result, canonical,
    GuardedNameExtension.connect_open_histories_in_original_names trace result opened quiet
      canonical.1.1 canonical.1.2.1 stable canonical.1.2.2.2.symm observe recovery commutative respect⟩

/-- A quiet trace has a canonical addressed survivor in the original name
set. The exact root word and checked endpoint observation survive both
episode excision and selection of the canonical schedule. -/
theorem normalize_to_canonical_schedule (trace : Trace (encodeProgram typedProgram) last)
    (quiet : Progress.Quiet (trace.state last)) (stable : ChildContinuations (encodeProgram typedProgram))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ (length : Nat) (reduced result : Trace (encodeProgram typedProgram) length) (expand : Nat → Nat),
      length ≤ last ∧ RetainedEvents trace reduced expand ∧
      Canonical (orchestrationInput reduced) result ∧ originalRoots result = originalRoots trace ∧
      GuardedConfluence.EndpointAgreement observe (trace.state last) (result.state length) ∧
      (addressedEvents reduced).Perm (addressedEvents result) ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath reduced result ∧
      (Nonempty (ClosedEpisode trace) → length < last) := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  obtain ⟨length, reduced, expand, bounded, shorter, reducedOpen, retained, roots, _, reducedQuiet, _, _, erased, related⟩ :=
    eliminate_closed_episodes_with_length trace quiet observe recovery commutative respect
  obtain ⟨result, canonical, path⟩ := canonical_path_in_original_names reduced reducedOpen reducedQuiet
    stable observe recovery commutative respect
  have resultRoots := same_root_commands result reduced path.input_eq
  obtain ⟨endpoint, events⟩ := path.preserves
  obtain ⟨names, compared⟩ := (ProjectedAgreement.of_related related).trans endpoint
  exact ⟨length, reduced, result, expand, bounded, retained, canonical, resultRoots.trans roots,
    ⟨names, _, _, erased, .refl _, compared⟩, events.symm, path, shorter⟩

/-- Explicit callback obligations shared by normalization clients. This is
not a typeclass: callers supply and can inspect all three contracts. -/
structure OperationContracts (ops : CoeffectOperations V) (observe : ∀ key, Setoid (V key)) : Prop where
  recovery : ValueOperationWitness ops
  commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key
  respect : ∀ key, OperationRespects ops key (observe key).r

/-- Named evidence for the canonical survivor of a quiet history.
The existential theorem above remains the paper-facing compatibility API. -/
structure NormalizationCertificate (trace : Trace (encodeProgram typedProgram) last)
    (observe : ∀ key, Setoid (V key)) where
  length : Nat
  reduced : Trace (encodeProgram typedProgram) length
  result : Trace (encodeProgram typedProgram) length
  expand : Nat → Nat
  bounded : length ≤ last
  retained : RetainedEvents trace reduced expand
  canonical : Canonical (orchestrationInput reduced) result
  roots : originalRoots result = originalRoots trace
  endpoint : GuardedConfluence.EndpointAgreement observe (trace.state last) (result.state length)
  events : (addressedEvents reduced).Perm (addressedEvents result)
  path : letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    GuardedCompleteAlignment.ScheduleAlignmentPath reduced result
  shorter : Nonempty (ClosedEpisode trace) → length < last

/-- Construct the named certificate using the general original-name theorem. -/
theorem normalization_certificate (trace : Trace (encodeProgram typedProgram) last)
    (quiet : Progress.Quiet (trace.state last)) (stable : ChildContinuations (encodeProgram typedProgram))
    (observe : ∀ key, Setoid (V key)) (contracts : OperationContracts ops observe) :
    Nonempty (NormalizationCertificate trace observe) := by
  obtain ⟨length, reduced, result, expand, bounded, retained, canonical, roots, endpoint, events, path, shorter⟩ :=
    normalize_to_canonical_schedule trace quiet stable observe
      contracts.recovery contracts.commutative contracts.respect
  exact ⟨⟨length, reduced, result, expand, bounded, retained, canonical, roots, endpoint, events, path, shorter⟩⟩

/-- Excision and a certified path in the original name set reach the
least candidate accessible from the chosen open reduction. The
global canonical word is reachable exactly when it equals this word. -/
theorem normalize_to_least_reachable_schedule (trace : Trace (encodeProgram typedProgram) last)
    (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ (length : Nat) (reduced moved : Trace (encodeProgram typedProgram) length) (expand : Nat → Nat),
      length ≤ last ∧ RetainedEvents trace reduced expand ∧
      (Nonempty (ClosedEpisode trace) → length < last) ∧
      Candidate (orchestrationInput reduced) moved ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath reduced moved ∧
      originalRoots moved = originalRoots trace ∧
      GuardedConfluence.EndpointAgreement observe (trace.state last) (moved.state length) ∧
      (addressedEvents moved).Perm (addressedEvents reduced) ∧
      ∀ other : Trace (encodeProgram typedProgram) length, Candidate (orchestrationInput reduced) other →
        GuardedCompleteAlignment.ScheduleAlignmentPath reduced other → priorityWord moved ≤ priorityWord other := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  obtain ⟨length, reduced, expand, bounded, shorter, reducedOpen, retained, roots, _, reducedQuiet, _, _, erased, related⟩ :=
    eliminate_closed_episodes_with_length trace quiet observe recovery commutative respect
  obtain ⟨moved, candidate, path, least⟩ := exists_least_reachable_schedule reduced reducedOpen reducedQuiet
  have movedRoots := same_root_commands moved reduced candidate.2.2.2
  have self := moved.self_related length (Nat.le_refl _)
    (TypedRegistry.encoded_program_callbacks ops observe typedProgram recovery commutative)
  have endpoint := GuardedConfluence.compare_endpoints_of_schedule_path observe erased (.refl _) related self path
  exact ⟨length, reduced, moved, expand, bounded, retained, shorter, candidate, path,
    movedRoots.trans roots, endpoint, path.preserves.2, least⟩

/-- Compatibility wrapper for callers supplying redraw availability. The
general normalization theorem now proves the result without using that premise. -/
theorem normalize_with_alignment_path (trace : Trace (encodeProgram typedProgram) last)
    (quiet : Progress.Quiet (trace.state last)) (stable : ChildContinuations (encodeProgram typedProgram))
    (redraw : ∀ {length : Nat} (reduced : Trace (encodeProgram typedProgram) length) (expand : Nat → Nat),
      length ≤ last → RetainedEvents trace reduced expand →
      (∃ pruned, VestigeErasures (trace.state last) pruned ∧
        GuardedIncarnationRedraw.LiveDomainRenaming pruned (reduced.state length)) →
      ∀ source : Trace (encodeProgram typedProgram) length,
        orchestrationInput source = orchestrationInput reduced →
        (addressedEvents source).Perm (addressedEvents reduced) →
        GuardedIncarnationRedraw.LiveDomainRenaming (reduced.state length) (source.state length) →
        GuardedCompleteAlignment.RedrawAtReuseFor source)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ (length : Nat) (reduced moved : Trace (encodeProgram typedProgram) length) (expand : Nat → Nat),
      length ≤ last ∧ RetainedEvents trace reduced expand ∧
      Canonical (orchestrationInput reduced) moved ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath reduced moved ∧
      originalRoots moved = originalRoots trace ∧
      GuardedConfluence.EndpointAgreement observe (trace.state last) (moved.state length) ∧
      (Nonempty (ClosedEpisode trace) → length < last) := by
  have _compatibility := @redraw
  obtain ⟨certificate⟩ := normalization_certificate trace quiet stable observe ⟨recovery, commutative, respect⟩
  exact ⟨certificate.length, certificate.reduced, certificate.result, certificate.expand,
    certificate.bounded, certificate.retained, certificate.canonical, certificate.path,
    certificate.roots, certificate.endpoint, certificate.shorter⟩

private theorem spare_of_distinct_names (used names : List Name) (distinct : names.Nodup)
    (room : used.length < names.length) : ∃ spare, spare ∈ names ∧ spare ∉ used := by
  induction used generalizing names with
  | nil =>
    cases names with
    | nil => simp at room
    | cons name rest => exact ⟨name, by simp, by simp⟩
  | cons named rest ih =>
    have shorter : rest.length < (names.erase named).length := by
      have dropped := List.le_length_erase (l := names) (a := named)
      simp only [List.length_cons] at room
      omega
    obtain ⟨spare, present, unused⟩ := ih _ (distinct.erase named) shorter
    have separate := (List.Nodup.mem_erase_iff distinct).mp present
    exact ⟨spare, separate.2, by simp [separate.1, unused]⟩

/-- The number of transitions that can allocate bounds the spare-name
requirement throughout excision and local alignment. -/
theorem normalize_with_birth_slot_supply (trace : Trace (encodeProgram typedProgram) last)
    (quiet : Progress.Quiet (trace.state last)) (stable : ChildContinuations (encodeProgram typedProgram))
    (names : List Name) (distinct : names.Nodup) (room : GuardedIncarnationRedraw.birthSlotsThrough trace last < names.length)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ (length : Nat) (reduced moved : Trace (encodeProgram typedProgram) length) (expand : Nat → Nat),
      length ≤ last ∧ RetainedEvents trace reduced expand ∧
      Canonical (orchestrationInput reduced) moved ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath reduced moved ∧
      originalRoots moved = originalRoots trace ∧
      GuardedConfluence.EndpointAgreement observe (trace.state last) (moved.state length) ∧
      (Nonempty (ClosedEpisode trace) → length < last) := by
  have _compatibility0 := distinct
  have _compatibility1 := room
  obtain ⟨certificate⟩ := normalization_certificate trace quiet stable observe ⟨recovery, commutative, respect⟩
  exact ⟨certificate.length, certificate.reduced, certificate.result, certificate.expand,
    certificate.bounded, certificate.retained, certificate.canonical, certificate.path,
    certificate.roots, certificate.endpoint, certificate.shorter⟩

/-- The release bound gives connectivity between the actual open
histories, with no need to extend the name type. Only the source
endpoint and recorded removals are counted. -/
theorem schedule_path_of_common_input_with_release_supply
    (left right : Trace (encodeProgram typedProgram) last)
    (leftOpen : ¬ Nonempty (ClosedEpisode left)) (rightOpen : ¬ Nonempty (ClosedEpisode right))
    (leftQuiet : Progress.Quiet (left.state last)) (rightQuiet : Progress.Quiet (right.state last))
    (stable : ChildContinuations (encodeProgram typedProgram))
    (input : orchestrationInput left = orchestrationInput right)
    (liveNames : List Name) (liveCover : ∀ name row, right.state last name = some row → name ∈ liveNames)
    (names : List Name) (distinct : names.Nodup)
    (room : liveNames.length + (GuardedReservationOrder.releasesBefore right last).length < names.length)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    GuardedCompleteAlignment.ScheduleAlignmentPath right left := by
  apply schedule_path_of_common_input_with_local_redraw left right leftOpen rightOpen leftQuiet rightQuiet
    stable input ?_ observe recovery commutative respect
  intro source same _ domain
  obtain ⟨live, size, covers⟩ := domain.map_cover liveNames liveCover
  obtain ⟨used, count, allCuts⟩ := GuardedIncarnationRedraw.history_name_cover_by_releases source live covers
  have sameReleases : GuardedReservationOrder.releasesBefore source last =
      GuardedReservationOrder.releasesBefore right last := by
    rw [GuardedReservationOrder.releases_of_input, GuardedReservationOrder.releases_of_input, same, input]
  rw [sameReleases, size] at count
  obtain ⟨spare, _, outside⟩ := spare_of_distinct_names used names distinct (by omega)
  apply GuardedCompleteAlignment.redrawAtReuseFor_of_spare source stable
  refine ⟨spare, fun cut bounded => ?_⟩
  cases found : source.state cut spare with
  | none => rfl
  | some row => exact False.elim (outside (allCuts cut bounded spare row found))

/-- A spare suffices when the name set is larger than an endpoint
cover plus the number of releases. Nonallocating stages cost no names. -/
theorem normalize_with_release_supply (trace : Trace (encodeProgram typedProgram) last)
    (quiet : Progress.Quiet (trace.state last)) (stable : ChildContinuations (encodeProgram typedProgram))
    (liveNames : List Name) (liveCover : ∀ name row, trace.state last name = some row → name ∈ liveNames)
    (names : List Name) (distinct : names.Nodup)
    (room : liveNames.length + (GuardedReservationOrder.releasesBefore trace last).length < names.length)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ (length : Nat) (reduced moved : Trace (encodeProgram typedProgram) length) (expand : Nat → Nat),
      length ≤ last ∧ RetainedEvents trace reduced expand ∧
      Canonical (orchestrationInput reduced) moved ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath reduced moved ∧
      originalRoots moved = originalRoots trace ∧
      GuardedConfluence.EndpointAgreement observe (trace.state last) (moved.state length) ∧
      (Nonempty (ClosedEpisode trace) → length < last) := by
  have _compatibility0 := liveCover
  have _compatibility1 := distinct
  have _compatibility2 := room
  obtain ⟨certificate⟩ := normalization_certificate trace quiet stable observe ⟨recovery, commutative, respect⟩
  exact ⟨certificate.length, certificate.reduced, certificate.result, certificate.expand,
    certificate.bounded, certificate.retained, certificate.canonical, certificate.path,
    certificate.roots, certificate.endpoint, certificate.shorter⟩

/-- A finite name set with more names than input transitions supports the entire
normalization path without changing the name type, even with removals
and reused draws. Each intermediate history can pick its own spare. -/
theorem normalize_with_bounded_name_supply (trace : Trace (encodeProgram typedProgram) last)
    (quiet : Progress.Quiet (trace.state last)) (stable : ChildContinuations (encodeProgram typedProgram))
    (names : List Name) (distinct : names.Nodup) (room : last < names.length)
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ (length : Nat) (reduced moved : Trace (encodeProgram typedProgram) length) (expand : Nat → Nat),
      length ≤ last ∧ RetainedEvents trace reduced expand ∧
      Canonical (orchestrationInput reduced) moved ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath reduced moved ∧
      originalRoots moved = originalRoots trace ∧
      GuardedConfluence.EndpointAgreement observe (trace.state last) (moved.state length) ∧
      (Nonempty (ClosedEpisode trace) → length < last) :=
  normalize_with_birth_slot_supply trace quiet stable names distinct
    (Nat.lt_of_le_of_lt (GuardedIncarnationRedraw.birthSlotsThrough_le trace last) room)
    observe recovery commutative respect

/-- Root-only orchestration admits a canonical exchange path after
episode excision in any original name set. Root removals and
reinsertions are permitted. -/
theorem normalize_root_only (trace : Trace (encodeProgram typedProgram) last)
    (quiet : Progress.Quiet (trace.state last)) (stable : ChildContinuations (encodeProgram typedProgram))
    (rootsOnly : RootOnlyInput (orchestrationInput trace))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ (length : Nat) (reduced moved : Trace (encodeProgram typedProgram) length) (expand : Nat → Nat),
      length ≤ last ∧ RetainedEvents trace reduced expand ∧
      Canonical (orchestrationInput reduced) moved ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath reduced moved ∧
      originalRoots moved = originalRoots trace ∧
      GuardedConfluence.EndpointAgreement observe (trace.state last) (moved.state length) ∧
      (Nonempty (ClosedEpisode trace) → length < last) := by
  have _compatibility0 := rootsOnly
  obtain ⟨certificate⟩ := normalization_certificate trace quiet stable observe ⟨recovery, commutative, respect⟩
  exact ⟨certificate.length, certificate.reduced, certificate.result, certificate.expand,
    certificate.bounded, certificate.retained, certificate.canonical, certificate.path,
    certificate.roots, certificate.endpoint, certificate.shorter⟩

/-- Equal literal root commands suffice for confluence after excision
when neither original history has explicit commands targeting children. -/
theorem confluence_of_root_only_input {rightLength : Nat}
    (left : Trace (encodeProgram typedProgram) last) (right : Trace (encodeProgram typedProgram) rightLength)
    (leftQuiet : Progress.Quiet (left.state last)) (rightQuiet : Progress.Quiet (right.state rightLength))
    (leftRoots : RootOnlyInput (orchestrationInput left)) (rightRoots : RootOnlyInput (orchestrationInput right))
    (commands : originalRoots left = originalRoots right)
    (stable : ChildContinuations (encodeProgram typedProgram))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    GuardedConfluence.EndpointAgreement observe (left.state last) (right.state rightLength) := by
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  obtain ⟨_, first, _, _, firstOpen, firstKept, firstRoots, _, firstQuiet, _, _, firstErased, firstRelated⟩ :=
    eliminate_closed_episodes left leftQuiet observe recovery commutative respect
  obtain ⟨_, second, _, _, secondOpen, secondKept, secondRoots, _, secondQuiet, _, _, secondErased, secondRelated⟩ :=
    eliminate_closed_episodes right rightQuiet observe recovery commutative respect
  have input := root_only_input_of_same_roots first second firstOpen firstQuiet secondOpen secondQuiet
    (retained_root_only_input firstKept leftRoots) (retained_root_only_input secondKept rightRoots)
    (firstRoots.trans (commands.trans secondRoots.symm))
  exact (GuardedConfluence.compare_surviving_endpoints observe first second firstErased secondErased
    firstRelated secondRelated stable firstOpen secondOpen firstQuiet secondQuiet input recovery commutative respect).1

/-- Normalization for a history with no removals. The statement is the
general certificate; it does not record that the retained history also has
no removals, or that the canonical exchange path needs no redraw. -/
theorem normalize_without_removals (trace : Trace (encodeProgram typedProgram) last)
    (quiet : Progress.Quiet (trace.state last)) (stable : ChildContinuations (encodeProgram typedProgram))
    (noRemovals : ∀ cut, cut < last → ∀ name, trace.event cut ≠ .command (.remove name))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, OperationRespects ops key (observe key).r) :
    letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
    ∃ (length : Nat) (reduced moved : Trace (encodeProgram typedProgram) length) (expand : Nat → Nat),
      length ≤ last ∧ RetainedEvents trace reduced expand ∧
      Canonical (orchestrationInput reduced) moved ∧
      GuardedCompleteAlignment.ScheduleAlignmentPath reduced moved ∧
      originalRoots moved = originalRoots trace ∧
      GuardedConfluence.EndpointAgreement observe (trace.state last) (moved.state length) ∧
      (Nonempty (ClosedEpisode trace) → length < last) := by
  have _compatibility0 := noRemovals
  obtain ⟨certificate⟩ := normalization_certificate trace quiet stable observe ⟨recovery, commutative, respect⟩
  exact ⟨certificate.length, certificate.reduced, certificate.result, certificate.expand,
    certificate.bounded, certificate.retained, certificate.canonical, certificate.path,
    certificate.roots, certificate.endpoint, certificate.shorter⟩

end Typed

end Cordis.Repairs.GuardedCanonicalSchedule
