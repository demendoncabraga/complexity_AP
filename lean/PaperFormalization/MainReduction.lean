import PaperFormalization.CantorEmbedding
import PaperFormalization.CantorExtension
import PaperFormalization.MainReductionAssembly

namespace PaperFormalization

/-- Banach–Mazur isometric universality of the real space C[0,1]. -/
theorem exists_banachAmbient_linearIsometry (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace.SeparableSpace E] : Nonempty (E →ₗᵢ[ℝ] BanachAmbient) := by
  obtain ⟨e⟩ := exists_cantorSpace_linearIsometry E
  let f : C(cantorSet, (ℕ → Bool)) :=
    ⟨cantorSetHomeomorphNatToBool, cantorSetHomeomorphNatToBool.continuous⟩
  exact ⟨cantorExtensionIsometry.comp
    ((continuousMapPrecompIsometry f cantorSetHomeomorphNatToBool.surjective).comp e)⟩

/-- The main Borel reduction for an arbitrary separable real Banach space. -/
theorem exists_borelReduction (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] :
    ∃ Φ : NatTree → BanachCode, Measurable Φ ∧
      (∀ T, T.IsWellFounded → ∀ p : RealBanachSpace → Prop, IsL1StableProperty p →
        p (RealBanachSpace.of (Φ T).val)) ∧
      (∀ T, T.IsIllFounded → IsometricOneComplementablyEmbeds E (Φ T).val) := by
  obtain ⟨P, hP, hIso⟩ := exists_l1_isometricQuotient (E := E)
  let _ := separableSpace_treeQuotient P
  obtain ⟨v⟩ := exists_banachAmbient_linearIsometry (TreeQuotient P)
  exact exists_borelReduction_of_ambientEmbedding P hP hIso v

end PaperFormalization
