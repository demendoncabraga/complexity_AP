import PaperFormalization.SuccessorOperators

namespace PaperFormalization

open Set Topology
open scoped ENNReal

/-- The tree of all finite prefixes of a branch. -/
def branchTree (b : ℕ → ℕ) : NatTree :=
  ⟨range (fun n : ℕ => List.ofFn fun j : Fin n => b j), by
    rintro s _ h ⟨n, rfl⟩
    have hlen : s.length ≤ n := by simpa using h.length_le
    refine ⟨s.length, ?_⟩
    exact (Fin.ofFn_take_eq_take_ofFn hlen (fun j : Fin n => b j)).trans
      (List.prefix_iff_eq_take.mp h).symm⟩

/-- Send every node coordinate to the node on the branch at the same depth. -/
noncomputable def branchProjection (b : ℕ → ℕ) : L1 (List ℕ) →L[ℝ] L1 (List ℕ) :=
  (branchInclusion b).comp collapseToDepth

theorem branchProjection_single (b : ℕ → ℕ) (s : List ℕ) (a : ℝ) :
    branchProjection b (lp.single 1 s a) = lp.single 1
      (List.ofFn fun j : Fin s.length => b j) a := by
  simp [branchProjection, branchInclusion, collapseToDepth, ← lp.single_smul]

theorem branchInclusion_mem_supported (b : ℕ → ℕ) (x : L1 ℕ) :
    branchInclusion b x ∈ supportedL1 (branchTree b) := by
  intro s hs
  let ev := lp.evalCLM ℝ (fun _ : List ℕ => ℝ) 1 s
  have h : ev.comp (branchInclusion b) = 0 := by
    apply l1Operator_ext
    intro n
    change branchInclusion b (lp.single 1 n 1) s = 0
    rw [branchInclusion, l1Operator_single, one_smul, lp.single_apply_ne]
    exact fun he => hs ⟨n, he.symm⟩
  exact DFunLike.congr_fun h x

theorem branchProjection_eq_self (b : ℕ → ℕ) (x : L1 (List ℕ))
    (hx : x ∈ supportedL1 (branchTree b)) : branchProjection b x = x := by
  have hs (s : List ℕ) : branchProjection b (lp.single 1 s (x s)) = lp.single 1 s (x s) := by
    by_cases hb : s ∈ (branchTree b).val
    · obtain ⟨n, rfl⟩ := hb
      simp only [branchProjection_single, List.length_ofFn, Fin.val_cast]
    · rw [show x s = 0 from hx s hb, lp.single_zero, map_zero]
  have h := lp.hasSum_single (p := 1) (by simp) x
  exact ((branchProjection b).hasSum h).unique (by simpa only [hs] using h)

theorem branchProjection_idempotent (b : ℕ → ℕ) (x : L1 (List ℕ)) :
    branchProjection b (branchProjection b x) = branchProjection b x :=
  branchProjection_eq_self b _ (branchInclusion_mem_supported b _)

theorem norm_branchProjection (b : ℕ → ℕ) : ‖branchProjection b‖ = 1 := by
  apply le_antisymm
  · calc
      _ ≤ ‖branchInclusion b‖ * ‖collapseToDepth‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul (norm_branchInclusion_le b) norm_collapseToDepth_le
        (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  · have h := (branchProjection b).le_opNorm (lp.single 1 ([] : List ℕ) (1 : ℝ))
    rw [branchProjection_single, lp.norm_single (by simp), lp.norm_single (by simp), norm_one,
      mul_one] at h
    exact h

/-- Enumerating a branch by depth identifies its supported ℓ₁ space with ℓ₁ on ℕ. -/
noncomputable def branchEnumerationIsometry (b : ℕ → ℕ) :
    supportedL1 (branchTree b) ≃ₗᵢ[ℝ] L1 ℕ := by
  let j : L1 ℕ →ₗᵢ[ℝ] supportedL1 (branchTree b) :=
    ⟨(branchInclusion b).toLinearMap.codRestrict _ (branchInclusion_mem_supported b), fun x => by
      change ‖branchInclusion b x‖ = ‖x‖
      apply le_antisymm
      · simpa only [one_mul] using (branchInclusion b).le_of_opNorm_le (norm_branchInclusion_le b) x
      · simpa only [collapseToDepth_branchInclusion, one_mul] using
          collapseToDepth.le_of_opNorm_le norm_collapseToDepth_le (branchInclusion b x)⟩
  exact (LinearIsometryEquiv.ofSurjective j fun x =>
    ⟨collapseToDepth x.val, Subtype.ext (branchProjection_eq_self b x.val x.property)⟩).symm

/-- The operator on a branch induced by an operator on ℓ₁. -/
noncomputable def branchOperator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : L1 ℕ →L[ℝ] E) (b : ℕ → ℕ) : supportedL1 (branchTree b) →L[ℝ] E :=
  P.comp (branchEnumerationIsometry b).toLinearIsometry.toContinuousLinearMap

theorem branchProjection_maps_branchKernelSpan {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (P : L1 ℕ →L[ℝ] E) (b : ℕ → ℕ) :
    (branchKernelSpan P).map (branchProjection b).toLinearMap ≤
      P.toLinearMap.ker.map (branchInclusion b).toLinearMap := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨collapseToDepth x, branchKernelSpan_le_depthKernel P hx, rfl⟩

theorem branchProjection_preserves_branchKernelSpan {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (P : L1 ℕ →L[ℝ] E) (b : ℕ → ℕ) :
    (branchKernelSpan P).map (branchProjection b).toLinearMap ≤ branchKernelSpan P :=
  (branchProjection_maps_branchKernelSpan P b).trans
    ((le_iSup (fun c : ℕ → ℕ => P.toLinearMap.ker.map (branchInclusion c).toLinearMap) b).trans
      (Submodule.le_topologicalClosure _))

/-- The branch projection in the ill-founded-tree proof has norm one and maps the
common kernel span into the chosen branch kernel. -/
theorem branchProjection_properties {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : L1 ℕ →L[ℝ] E) (b : ℕ → ℕ) :
    ‖branchProjection b‖ = 1 ∧
      (∀ x, branchProjection b (branchProjection b x) = branchProjection b x) ∧
      (branchKernelSpan P).map (branchProjection b).toLinearMap ≤
        P.toLinearMap.ker.map (branchInclusion b).toLinearMap ∧
      (branchKernelSpan P).map (branchProjection b).toLinearMap ≤ branchKernelSpan P :=
  ⟨norm_branchProjection b, branchProjection_idempotent b,
    branchProjection_maps_branchKernelSpan P b, branchProjection_preserves_branchKernelSpan P b⟩

end PaperFormalization
