import PaperFormalization.BorelAssignment

namespace PaperFormalization.ClosedSubspaces

open Set TopologicalSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem measurableSet_hit {U : Set E} (hU : IsOpen U) :
    MeasurableSet (hit U) :=
  MeasurableSpace.measurableSet_generateFrom ⟨U, hU, rfl⟩

theorem eq_of_hit_countableBasis [SecondCountableTopology E] (W Z : ClosedSubspaces E)
    (h : ∀ U ∈ countableBasis E, W ∈ hit U ↔ Z ∈ hit U) : W = Z := by
  have hsub (A B : ClosedSubspaces E)
      (hab : ∀ U ∈ countableBasis E, A ∈ hit U → B ∈ hit U) :
      (A.val : Set E) ⊆ B.val := by
    intro x hx
    by_contra hxB
    have hn : (B.val : Set E)ᶜ ∈ 𝓝 x := B.property.isOpen_compl.mem_nhds hxB
    obtain ⟨U, hU, hxU, hsub⟩ := (isBasis_countableBasis E).mem_nhds_iff.mp hn
    obtain ⟨y, hyB, hyU⟩ := hab U hU ⟨x, hx, hxU⟩
    exact (hsub hyU) hyB
  exact Subtype.ext (SetLike.coe_injective
    (Set.Subset.antisymm (hsub W Z fun U hU => (h U hU).mp)
      (hsub Z W fun U hU => (h U hU).mpr)))

/-- The closed-subspace coding has measurable equality. -/
theorem measurableSet_eq_of_measurable [SecondCountableTopology E] {A : Type*} [MeasurableSpace A]
    {f g : A → ClosedSubspaces E} (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {a : A | f a = g a} := by
  let B := countableBasis E
  let _ : Countable B := (countable_countableBasis E).to_subtype
  let left (U : B) := f ⁻¹' hit U.val
  let right (U : B) := g ⁻¹' hit U.val
  have he : {a : A | f a = g a} =
      ⋂ U : B, (left U ∩ right U) ∪ ((left U)ᶜ ∩ (right U)ᶜ) := Set.ext fun a =>
    ⟨fun h => Set.mem_iInter.mpr fun U => by
      change (f a ∈ hit U.val ∧ g a ∈ hit U.val) ∨
        (f a ∉ hit U.val ∧ g a ∉ hit U.val)
      change f a = g a at h
      rw [h]
      tauto,
      fun h => eq_of_hit_countableBasis (f a) (g a) fun U hU => by
        have hm := Set.mem_iInter.mp h ⟨U, hU⟩
        change (f a ∈ hit U ∧ g a ∈ hit U) ∨ (f a ∉ hit U ∧ g a ∉ hit U) at hm
        tauto⟩
  rw [he]
  exact MeasurableSet.iInter fun U => by
    have hU := measurableSet_hit ((isBasis_countableBasis E).isOpen U.property)
    have hL := hf hU
    have hR := hg hU
    exact (hL.inter hR).union (hL.compl.inter hR.compl)

end PaperFormalization.ClosedSubspaces
