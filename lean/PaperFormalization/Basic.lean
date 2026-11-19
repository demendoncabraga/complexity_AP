import Mathlib

namespace PaperFormalization

/-- The approximation property for a real normed space. -/
def HasApproximationProperty (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ K : Set E, IsCompact K →
    ∃ A : E →L[ℝ] E, FiniteDimensional ℝ A.toLinearMap.range ∧
      ∀ x ∈ K, ‖x - A x‖ ≤ ε

/-- An isomorphic complemented copy, expressed by a bounded linear retraction. -/
def ComplementablyEmbeds (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : Prop :=
  ∃ i : E →L[ℝ] F, ∃ r : F →L[ℝ] E, Function.LeftInverse r i

/-- An isometric copy with a projection of norm at most one. -/
def IsometricOneComplementablyEmbeds (E F : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] : Prop :=
  ∃ i : E →ₗᵢ[ℝ] F, ∃ r : F →L[ℝ] E, ‖r‖ ≤ 1 ∧ Function.LeftInverse r i

/-- Trees of natural numbers include the empty tree. -/
def NatTree := {T : Set (List ℕ) // ∀ s t, s <+: t → t ∈ T → s ∈ T}

namespace NatTree

/-- The branches are infinite sequences whose every finite prefix lies in the tree. -/
def branches (T : NatTree) : Set (ℕ → ℕ) :=
  {b | ∀ n, List.ofFn (fun i : Fin n => b i) ∈ T.val}

/-- Well-foundedness in the manuscript is absence of an infinite branch. -/
def IsWellFounded (T : NatTree) : Prop := T.branches = ∅

/-- Ill-founded trees admit an infinite branch. -/
def IsIllFounded (T : NatTree) : Prop := T.branches.Nonempty

end NatTree
end PaperFormalization
