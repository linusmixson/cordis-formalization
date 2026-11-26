import Cordis.Repairs.GuardedCanonicalSchedule

/-! A nonempty operation family meeting all three `OperationContracts`
used by the repaired Theorem 80: an integer counter at one key whose
operations add an argument and whose captured inverse subtracts it.
The three contracts are the repository's own `OperationContracts`, used
unchanged. -/
namespace Cordis.Repairs.CounterContracts
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PaperObservationEquations (OperationRespects CommutativeKey IndependentOperations eq41 OperationMonoid)
open PartialCoeffectLifting (Table PartialMap liftMap liftOperation compose)
open PartialCoeffectIndependenceContracts (tableSetoid OperationGenerator)
open PartialInverseObservation (MapRelated)
open Iterators (OptionRel)

abbrev V : Unit → Type := fun _ => Int

/-- One operation name; `x` is the amount added. -/
def ops : CoeffectOperations V where
  Name _ := PUnit
  Argument _ _ := Int
  Outcome _ _ := PUnit
  operation _ _ x := ⟨fun v => some (v + x, fun w => some (w - x), PUnit.unit)⟩

def observe (_ : Unit) : Setoid Int := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩

abbrev T := Table V

/-- Translation of the single binding, undefined when it is absent. -/
def shift (c : Int) : PartialMap T := fun t => (t ()).map (fun v _ => some (v + c))

inductive Good : PartialMap T → Prop
  | identity : Good some
  | shift (c : Int) : Good (shift c)

theorem update_unit (v : Option Int) (t : T) : Coeffects.update () v t = fun _ => v := by
  funext j
  cases j
  simp [Coeffects.update]

theorem liftMap_sub (x : Int) : liftMap () (fun w : Int => some (w - x)) = shift (-x) := by
  funext t
  cases h : t () <;> simp [liftMap, shift, h, update_unit, Int.sub_eq_add_neg]

theorem lift_run (a : PUnit) (x : Int) (t : T) :
    (liftOperation () (ops.operation () a x)).run t =
      (t ()).map (fun v => ((fun _ => some (v + x) : T), shift (-x), PUnit.unit)) := by
  cases h : t () <;> simp [liftOperation, ops, h, update_unit, ← liftMap_sub]

theorem good_compose {f g : PartialMap T} (hf : Good f) (hg : Good g) : Good (compose f g) := by
  cases hf with
  | identity =>
    have : compose some g = g := by funext t; cases h : g t <;> simp [compose, h]
    rw [this]; exact hg
  | shift a =>
    cases hg with
    | identity =>
      have : compose (shift a) some = shift a := by funext t; rfl
      rw [this]; exact .shift a
    | shift b =>
      have : compose (shift a) (shift b) = shift (b + a) := by
        funext t
        cases h : t () <;> simp [compose, shift, h, Int.add_assoc]
      rw [this]; exact .shift _

theorem good_comm {f g : PartialMap T} (hf : Good f) (hg : Good g) : compose f g = compose g f := by
  cases hf with
  | identity => funext t; cases h : g t <;> simp [compose, h]
  | shift a =>
    cases hg with
    | identity => funext t; cases h : shift a t <;> simp [compose, h]
    | shift b =>
      funext t
      cases h : t () <;> simp [compose, shift, h, Int.add_assoc, Int.add_comm a b]

theorem generated_good {generators : PartialMap T → Prop} (each : ∀ m, generators m → Good m)
    {g : PartialMap T} (generated : PartialMapClosure.Generated generators g) : Good g := by
  induction generated with
  | identity => exact .identity
  | generator found => exact each _ found
  | composition _ _ left right => exact good_compose left right

/-- Good maps preserve whether the binding is present. -/
theorem good_presence {g : PartialMap T} (hg : Good g) {before after : T} (moved : g before = some after) :
    (after ()).isSome = (before ()).isSome := by
  cases hg with
  | identity => cases moved; rfl
  | shift c =>
    cases h : before () <;> simp [shift, h] at moved
    subst moved
    rfl

abbrev related : Setoid T := tableSetoid observe (fun _ => True)

theorem related_eq {x y : T} (h : related.r x y) : x = y := by
  funext k
  cases k
  have pair := h () trivial
  cases hx : x () <;> cases hy : y () <;> simp only [hx, hy, OptionRel] at pair
  · rfl
  · exact congrArg some pair

theorem maps_self (m : PartialMap T) : MapRelated related.r m m := by
  intro x y h
  rw [related_eq h]
  cases m y with
  | none => trivial
  | some z => exact related.refl z

theorem operation_generator_good (a : PUnit) {m : PartialMap T}
    (found : ∃ x, OperationGenerator (liftOperation () (ops.operation () a x)) m) : Good m := by
  obtain ⟨x, found⟩ := found
  cases found with
  | forward =>
    have : PartialCoeffectLifting.forward (liftOperation () (ops.operation () a x)) = shift x := by
      funext t
      cases h : t () <;> simp [PartialCoeffectLifting.forward, lift_run, h, shift]
    rw [this]; exact .shift x
  | inverse input output inverse outcome called =>
    rw [lift_run] at called
    cases h : input () <;> simp [h] at called
    rw [← called.2.1]; exact .shift _

abbrev stageOf (a : PUnit) (x : Int) : PartialIterators.Iterator T :=
  PartialIterators.stage (liftOperation () (ops.operation () a x)) (fun _ => none)

theorem stage_run (a : PUnit) (x : Int) (t : T) :
    (stageOf a x).run t = (t ()).map (fun v => ((fun _ => some (v + x) : T), shift (-x), none)) := by
  cases h : t () <;>
    simp [stageOf, PartialIterators.stage, PartialIterators.Iterator.run, lift_run, h]

theorem reach_root {a : PUnit} {x : Int} {current : PartialIterators.Iterator T}
    (reached : PartialIterators.Reach (stageOf a x) current) : current = stageOf a x := by
  induction reached with
  | root => rfl
  | continuation _ input output inverse selected ih =>
    subst ih
    rw [stage_run] at selected
    cases h : input () <;> simp [h] at selected

theorem generator_good (a : PUnit) (x : Int) {m : PartialMap T}
    (found : PartialMediatedIndependence.Generator (stageOf a x) m) : Good m := by
  cases found with
  | forward reached =>
    rw [reach_root reached]
    have : PartialMediatedIndependence.forward (stageOf a x) = shift x := by
      funext t
      cases h : t () <;> simp [PartialMediatedIndependence.forward, stage_run, h, shift]
    rw [this]; exact .shift x
  | inverse reached input output inverse tail called =>
    rw [reach_root reached, stage_run] at called
    cases h : input () <;> simp [h] at called
    rw [← called.2.1]; exact .shift _

theorem yield_preserved (a : PUnit) (x : Int) {g : PartialMap T} (hg : Good g) :
    PartialMapClosure.Preserves (PartialIteratorRelationLaws.YieldRel related)
      (PartialIteratorRelationLaws.observe (stageOf a x)) g := by
  intro before after moved
  have presence := good_presence hg moved
  simp only [PartialIteratorRelationLaws.observe, stage_run]
  cases hb : before () <;> cases ha : after () <;> simp [hb, ha] at presence
  · trivial
  · exact ⟨maps_self _, trivial⟩

theorem independent (a b : PUnit) (x y : Int) :
    PartialObservedIteratorIndependence.Independent related (stageOf a x) (stageOf b y) where
  commute f left g right := by
    have hf := generated_good (fun _ found => generator_good a x found) left
    have hg := generated_good (fun _ found => generator_good b y found) right
    change MapRelated related.r (compose f g) (compose g f)
    rw [good_comm hf hg]
    exact maps_self _
  left_yield current reached g right := by
    rw [reach_root reached]
    exact yield_preserved a x (generated_good (fun _ found => generator_good b y found) right)
  right_yield current reached f left := by
    rw [reach_root reached]
    exact yield_preserved b y (generated_good (fun _ found => generator_good a x found) left)

theorem outcomes_stable (a b : PUnit) : eq41 ops () () a b := by
  intro x g monoid σ σ' moved
  have presence := good_presence
    (generated_good (fun _ found => operation_generator_good b found) monoid) moved
  rw [lift_run, lift_run]
  cases h : σ () <;> cases h' : σ' () <;> simp [h, h'] at presence ⊢

theorem commutative : CommutativeKey ops related () := fun a b =>
  ⟨fun x y => independent a b x y, outcomes_stable a b, outcomes_stable b a⟩

theorem recovery : ValueOperationWitness ops := by
  intro k a x v w g b called
  simp only [ops, Option.some.injEq, Prod.mk.injEq] at called
  obtain ⟨rfl, rfl, _⟩ := called
  simp

theorem respect : OperationRespects ops () (observe ()).r := by
  intro a x v w h
  change v = w at h
  subst h
  refine ⟨rfl, ?_, rfl⟩
  intro y z hyz
  change y = z at hyz
  subst hyz
  rfl

/-- The three operation laws of the repaired Theorem 80 hold together for
a family with real operations, not only for the empty families used in
the repository's examples. -/
theorem contracts : GuardedCanonicalSchedule.OperationContracts ops observe :=
  ⟨recovery, fun _ => commutative, fun _ => respect⟩

end Cordis.Repairs.CounterContracts
