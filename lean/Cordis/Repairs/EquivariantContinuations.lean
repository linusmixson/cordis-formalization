import Cordis.Repairs.GuardedLandingMatching

/-! Continuations that ignore child names only up to renaming. While `Code`
carries no names, invariance of a birth's continuation under every
permutation of names is the same contract as `ChildContinuations`:
permutations act transitively on names. A weaker equivariant contract
therefore needs a name action on `Code` itself. -/
namespace Cordis.Repairs.EquivariantContinuations
open Calculus Stages GuardedLandingMatching

universe u
variable {Name Key Value Code Error : Type u} [DecidableEq Name] [DecidableEq Key]
local notation "P" => Renaming.Permutation Name
local notation "Program" => Code → Instruction Name Key Value Code Error

/-- The transposition of two names. -/
def transpose (a b : Name) : P where
  toFun n := if n = a then b else if n = b then a else n
  invFun n := if n = a then b else if n = b then a else n
  left_inv n := by
    by_cases ha : n = a <;> by_cases hb : n = b <;> simp_all
  right_inv n := by
    by_cases ha : n = a <;> by_cases hb : n = b <;> simp_all

theorem transpose_left (a b : Name) : (transpose a b).toFun a = b := by
  simp [transpose]

/-- A birth's continuation is invariant under every renaming of the drawn
child, with `Code` acted on trivially. -/
def InvariantContinuations (program : Program) : Prop :=
  ∀ (χ : P) code component, (program code).action = .instantiate component →
    ∀ child, (program code).next (.child (χ.toFun child)) = (program code).next (.child child)

omit [DecidableEq Key] in
/-- With a trivial action on `Code`, permutation invariance is exactly
`ChildContinuations`. -/
theorem invariant_iff_childContinuations (program : Program) :
    InvariantContinuations program ↔ ChildContinuations program := by
  constructor
  · intro invariant code component action child otherChild
    have moved := invariant (transpose child otherChild) code component action child
    rw [transpose_left] at moved
    exact moved.symm
  · intro stable χ code component action child
    exact stable code component action _ _

end Cordis.Repairs.EquivariantContinuations
