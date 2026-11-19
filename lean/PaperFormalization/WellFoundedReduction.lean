import PaperFormalization.BanachProperties
import PaperFormalization.WellFoundedSplit

namespace PaperFormalization

open scoped ENNReal

universe u

/-- A well-founded tree yields a space satisfying every property in the paper's class. -/
theorem wellFounded_treeSpace_has_property (T : NatTree) (hT : T.IsWellFounded)
    (p : RealBanachSpace → Prop) (hp : IsL1StableProperty p)
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : L1 ℕ →L[ℝ] E) : p (RealBanachSpace.of (treeSpace P T)) := by
  let Q (S : NatTree) := ∀ (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (A : L1 ℕ →L[ℝ] F), p (RealBanachSpace.of (treeSpace A S))
  suffices h : Q T from h E P
  refine NatTree.induction_on_successors hT ?_
  intro S ih F _ _ _ A
  by_cases hroot : [] ∈ S.val
  · let R := (treeRootLine A).comap (treeSpace A S).subtype
    have hdim := treeSpace_root_finiteDimensional A S
    let _ : FiniteDimensional ℝ R := hdim.1
    let _ : CompleteSpace R := (Submodule.closed_of_finiteDimensional R).completeSpace_coe
    let Y (m : ℕ) := RealBanachSpace.of (treeSpace (tailOperator A) (S.successor m))
    have hY (m : ℕ) : p (Y m) := by
      by_cases hm : [m] ∈ S.val
      · exact ih m hm (F ⧸ rootImage A) (tailOperator A)
      · let _ : Subsingleton (Y m) := Submodule.subsingleton_iff_eq_bot.mpr
          (treeSpace_successor_eq_bot_of_not_mem A S m hm)
        exact hp.of_subsingleton (Y m)
    obtain ⟨e⟩ := treeSpace_equiv_root_prod_successorSum A S hroot
    exact hp.invariant e (hp.prod (RealBanachSpace.of R)
      (RealBanachSpace.of (lp (fun m => (Y m : Type)) 1))
      (hp.of_finrank_le_one (RealBanachSpace.of R) hdim.2) (hp.sum Y hY))
  · have hleaf : S.val ⊆ {[]} := fun s hs => False.elim
      (hroot (S.property [] s List.nil_prefix hs))
    have hdim := treeSpace_finiteDimensional_of_root_only A S hleaf
    let _ : FiniteDimensional ℝ (treeSpace A S) := hdim.1
    exact hp.of_finrank_le_one (RealBanachSpace.of (treeSpace A S)) hdim.2

end PaperFormalization
