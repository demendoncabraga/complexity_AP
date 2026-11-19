import PaperFormalization.TreeReduction
import PaperFormalization.TreeTopology

namespace PaperFormalization

/-- Closed real linear subspaces of the ambient normed space. -/
def ClosedSubspaces (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  {W : Submodule ℝ E // IsClosed (W : Set E)}

namespace ClosedSubspaces

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The open-hit generator of the Effros measurable space. -/
def hit (U : Set E) : Set (ClosedSubspaces E) :=
  {W | ((W.val : Set E) ∩ U).Nonempty}

instance effros : MeasurableSpace (ClosedSubspaces E) :=
  MeasurableSpace.generateFrom {B | ∃ U : Set E, IsOpen U ∧ B = hit U}

/-- The closed span of the vectors indexed by nodes of a tree. -/
noncomputable def spanOfNodes (v : List ℕ → E) (T : NatTree) : ClosedSubspaces E :=
  ⟨(Submodule.span ℝ (v '' T.val)).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩

theorem spanOfNodes_hit_iff (v : List ℕ → E) (T : NatTree) {U : Set E} (hU : IsOpen U) :
    spanOfNodes v T ∈ hit U ↔ ∃ F : Finset (List ℕ), (↑F : Set (List ℕ)) ⊆ T.val ∧
      (((Submodule.span ℝ (v '' (F : Set (List ℕ)))) : Set E) ∩ U).Nonempty := by
  change (closure (Submodule.span ℝ (v '' T.val) : Set E) ∩ U).Nonempty ↔ _
  rw [closure_inter_open_nonempty_iff hU]
  exact ⟨fun ⟨x, hx, hxU⟩ => by
    obtain ⟨l, hl, hxl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℝ).mp hx
    exact ⟨l.support, (Finsupp.mem_supported ℝ l).mp hl,
      x, (Finsupp.mem_span_image_iff_linearCombination ℝ).mpr
        ⟨l, (Finsupp.mem_supported ℝ l).mpr subset_rfl, hxl⟩, hxU⟩,
    fun ⟨F, hF, x, hx, hxU⟩ =>
      ⟨x, Submodule.span_mono (Set.image_mono hF) hx, hxU⟩⟩

theorem measurable_spanOfNodes (v : List ℕ → E) : Measurable (spanOfNodes v) := by
  apply measurable_generateFrom
  rintro B ⟨U, hU, rfl⟩
  let G := {F : Finset (List ℕ) |
    (((Submodule.span ℝ (v '' (F : Set (List ℕ)))) : Set E) ∩ U).Nonempty}
  have he : spanOfNodes v ⁻¹' hit U =
      ⋃ F : G, ⋂ s : F.val, {T : NatTree | s.val ∈ T.val} :=
    Set.ext fun T => (spanOfNodes_hit_iff v T hU).trans
      ⟨fun ⟨F, hF, hFU⟩ => Set.mem_iUnion.mpr
        ⟨⟨F, hFU⟩, Set.mem_iInter.mpr fun s => hF s.property⟩,
        fun h => (Set.mem_iUnion.mp h).elim fun F hF =>
          ⟨F.val, fun s hs => Set.mem_iInter.mp hF ⟨s, hs⟩, F.property⟩⟩
  exact he.symm ▸ MeasurableSet.iUnion (fun F : G =>
    MeasurableSet.iInter fun s : F.val => (NatTree.isClopen_nodes s.val).2.measurableSet)

end ClosedSubspaces

/-- The manuscript's standard ambient space of real continuous functions on [0,1]. -/
abbrev BanachAmbient := C(Set.Icc (0 : ℝ) 1, ℝ)

/-- The Effros coding of separable Banach spaces by closed real subspaces of C[0,1]. -/
abbrev BanachCode := ClosedSubspaces BanachAmbient

section TreeAssignment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {P : L1 ℕ →L[ℝ] E}

/-- Assign the coded image of the reduction space, using one ambient isometric embedding. -/
noncomputable def treeAssignment (v : TreeQuotient P →ₗᵢ[ℝ] BanachAmbient) (T : NatTree) :
    BanachCode :=
  ClosedSubspaces.spanOfNodes (fun s => v ((branchKernelSpan P).mkQ (lp.single 1 s 1))) T

theorem measurable_treeAssignment (v : TreeQuotient P →ₗᵢ[ℝ] BanachAmbient) :
    Measurable (treeAssignment v) :=
  ClosedSubspaces.measurable_spanOfNodes _

theorem treeAssignment_eq_map (v : TreeQuotient P →ₗᵢ[ℝ] BanachAmbient) (T : NatTree) :
    (treeAssignment v T).val = (treeSpace P T).map v.toLinearMap := by
  apply SetLike.coe_injective
  let w : List ℕ → TreeQuotient P := fun s => (branchKernelSpan P).mkQ (lp.single 1 s 1)
  change closure (Submodule.span ℝ ((v ∘ w) '' T.val) : Set BanachAmbient) =
    v '' closure (Submodule.span ℝ (w '' T.val) : Set (TreeQuotient P))
  have hspan : (Submodule.span ℝ ((v ∘ w) '' T.val) : Set BanachAmbient) =
      v '' (Submodule.span ℝ (w '' T.val) : Set (TreeQuotient P)) :=
    (congrArg (fun S : Set BanachAmbient => (Submodule.span ℝ S : Set BanachAmbient))
      (Set.image_image v w T.val).symm).trans
      (congrArg (fun S : Submodule ℝ BanachAmbient => (S : Set BanachAmbient))
        (Submodule.map_span v.toLinearMap (w '' T.val)).symm)
  exact (congrArg closure hspan).trans (v.isometry.isClosedEmbedding.closure_image_eq _)

/-- The coded output represents the reduction space isometrically. -/
noncomputable def treeAssignment_isometry (v : TreeQuotient P →ₗᵢ[ℝ] BanachAmbient) (T : NatTree) :
    treeSpace P T ≃ₗᵢ[ℝ] (treeAssignment v T).val :=
  (LinearIsometryEquiv.ofSurjective (v.submoduleMap (treeSpace P T))
    (v.toLinearMap.submoduleMap_surjective (treeSpace P T))).trans
    (LinearIsometryEquiv.ofEq _ _ (treeAssignment_eq_map v T).symm)

end TreeAssignment
end PaperFormalization
