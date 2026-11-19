import PaperFormalization.EffrosSelectors
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

namespace PaperFormalization.ClosedSubspaces

open Set Topology TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def spanOfSequence (d : ℕ → E) : ClosedSubspaces E :=
  ⟨(Submodule.span ℝ (range d)).topologicalClosure, isClosed_closure⟩

section RationalSpan

noncomputable local instance : Module ℚ E := Module.restrictScalars ℚ ℝ E
local instance : IsScalarTower ℚ ℝ E := IsScalarTower.restrictScalars ℚ ℝ E
local instance : ContinuousConstSMul ℚ E :=
  ⟨fun q => show Continuous (fun x : E => (q : ℝ) • x) from continuous_const_smul _⟩

private theorem coe_spanOfSequence (d : ℕ → E) :
    ((spanOfSequence d).val : Set E) = closure (Submodule.span ℚ (range d) : Set E) := by
  let V := (Submodule.span ℚ (range d)).topologicalClosure
  let W : Submodule ℝ E :=
    { carrier := V
      zero_mem' := V.zero_mem
      add_mem' := V.add_mem
      smul_mem' := fun a x hx => by
        apply Rat.denseRange_cast.induction_on a (p := fun b : ℝ => b • x ∈ V)
        · exact isClosed_closure.preimage (continuous_id.smul continuous_const)
        · intro q
          exact V.smul_mem q hx }
  change closure (Submodule.span ℝ (range d) : Set E) = (V : Set E)
  apply le_antisymm
  · apply closure_minimal _ isClosed_closure
    exact (show Submodule.span ℝ (range d) ≤ W from Submodule.span_le.mpr fun x hx =>
      subset_closure (Submodule.subset_span hx : x ∈ Submodule.span ℚ (range d)))
  · apply closure_mono
    exact (show Submodule.span ℚ (range d) ≤
        (Submodule.span ℝ (range d)).restrictScalars ℚ from
      Submodule.span_le.mpr fun x hx => Submodule.subset_span hx)

theorem measurable_spanOfSequence [SeparableSpace E] [MeasurableSpace E] [BorelSpace E] :
    Measurable (spanOfSequence (E := E)) := by
  apply measurable_generateFrom
  rintro _ ⟨U, hU, rfl⟩
  have he : spanOfSequence (E := E) ⁻¹' hit U =
      ⋃ q : ℕ →₀ ℚ, {d : ℕ → E | (q.sum fun i a => (a : ℝ) • d i) ∈ U} := by
    ext d
    change (((spanOfSequence d).val : Set E) ∩ U).Nonempty ↔ _
    rw [coe_spanOfSequence, closure_inter_open_nonempty_iff hU]
    simp only [mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, hxU⟩
      obtain ⟨q, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
      exact ⟨q, hxU⟩
    · rintro ⟨q, hq⟩
      exact ⟨_, Finsupp.mem_span_range_iff_exists_finsupp.mpr ⟨q, rfl⟩, hq⟩
  rw [he]
  apply MeasurableSet.iUnion
  intro q
  have hq : Continuous (fun d : ℕ → E => q.sum fun i a => (a : ℝ) • d i) :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).const_smul _
  exact hq.measurable hU.measurableSet

end RationalSpan

theorem spanOfSequence_eq_of_closure (d : ℕ → E) (W : ClosedSubspaces E)
    (hd : closure (range d) = (W.val : Set E)) : spanOfSequence d = W := by
  apply Subtype.ext
  apply SetLike.coe_injective
  change closure (Submodule.span ℝ (range d) : Set E) = (W.val : Set E)
  apply le_antisymm
  · apply closure_minimal _ W.property
    exact Submodule.span_le.mpr (hd ▸ subset_closure)
  · rw [← hd]
    exact closure_mono Submodule.subset_span

instance standardBorelSpace [CompleteSpace E] [SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E] : StandardBorelSpace (ClosedSubspaces E) := by
  obtain ⟨g, hg, hclosure⟩ := exists_borel_dense_selectors (E := E)
  let code (W : ClosedSubspaces E) (n : ℕ) := g n W
  have hc : Measurable code := measurable_pi_lambda _ hg
  have hleft (W : ClosedSubspaces E) : spanOfSequence (code W) = W :=
    spanOfSequence_eq_of_closure _ _ (hclosure W)
  let S := {d | code (spanOfSequence d) = d}
  have hS : MeasurableSet S := measurableSet_eq_fun (hc.comp measurable_spanOfSequence) measurable_id
  have := hS.standardBorel
  have hcode (W : ClosedSubspaces E) : code W ∈ S := by
    change code (spanOfSequence (code W)) = code W
    rw [hleft]
  let e : ClosedSubspaces E ≃ᵐ S :=
    { toFun := fun W => ⟨code W, hcode W⟩
      invFun := fun d => spanOfSequence d.val
      left_inv := hleft
      right_inv := fun d => Subtype.ext d.property
      measurable_toFun := hc.subtype_mk (h := hcode)
      measurable_invFun := measurable_spanOfSequence.comp measurable_subtype_coe }
  let up := upgradeStandardBorel S
  let τ := TopologicalSpace.induced e up.toTopologicalSpace
  refine ⟨τ, ?_, @Equiv.polishSpace_induced _ _ up.toTopologicalSpace up.toPolishSpace e.toEquiv⟩
  constructor
  rw [show @borel _ τ = _ from borel_comap, ← eq_borel_upgradeStandardBorel]
  exact e.measurableEmbedding.comap_eq.symm

end PaperFormalization.ClosedSubspaces

namespace PaperFormalization

noncomputable instance : MeasurableSpace BanachAmbient := borel BanachAmbient

instance : BorelSpace BanachAmbient := ⟨rfl⟩

theorem banachCode_standardBorel : StandardBorelSpace BanachCode := inferInstance

end PaperFormalization
