import PaperFormalization.TreeTopology
import PaperFormalization.AnalyticPreimage

namespace PaperFormalization.NatTree

open Filter Set Topology

variable {X : Type*} [MetricSpace X]

/-- A node belongs to the tree of x when a branch extending it gives a close approximation to x. -/
noncomputable def approximationTree (f : (ℕ → ℕ) → X) (x : X) : NatTree :=
  ⟨{s | ∃ b : ℕ → ℕ, (∀ i (hi : i < s.length), s[i] = b i) ∧
      dist x (f b) < (1 / 2 : ℝ) ^ s.length},
    fun s t hst ⟨b, hb, hd⟩ => ⟨b, fun i hi =>
      (hst.getElem hi).trans (hb i (hi.trans_le hst.length_le)),
      hd.trans_le (pow_right_anti₀ (by norm_num) (by norm_num) hst.length_le)⟩⟩

theorem isOpen_mem_approximationTree (f : (ℕ → ℕ) → X) (s : List ℕ) :
    IsOpen {x : X | s ∈ (approximationTree f x).val} := by
  let B := {b : ℕ → ℕ | ∀ i (hi : i < s.length), s[i] = b i}
  have he : {x : X | s ∈ (approximationTree f x).val} =
      ⋃ b : B, Metric.ball (f b.val) ((1 / 2 : ℝ) ^ s.length) :=
    Set.ext fun x =>
      ⟨fun ⟨b, hb, hd⟩ => Set.mem_iUnion.mpr ⟨⟨b, hb⟩, hd⟩,
        fun h => (Set.mem_iUnion.mp h).elim fun b hb => ⟨b.val, b.property, hb⟩⟩
  exact he.symm ▸ isOpen_iUnion fun _ => Metric.isOpen_ball

theorem measurable_approximationTree [MeasurableSpace X] [BorelSpace X] (f : (ℕ → ℕ) → X) :
    Measurable (approximationTree f) := by
  apply isClosedEmbedding_code.measurableEmbedding.measurable_comp_iff.mp
  apply measurable_pi_iff.mpr
  intro s
  apply measurable_to_bool
  have he : (fun x => code (approximationTree f x) s) ⁻¹' {true} =
      {x : X | s ∈ (approximationTree f x).val} :=
    Set.ext fun x => by simp [code]
  exact he.symm ▸ (isOpen_mem_approximationTree f s).measurableSet

theorem approximationTree_illFounded_iff {f : (ℕ → ℕ) → X} (hf : Continuous f) (x : X) :
    (approximationTree f x).IsIllFounded ↔ x ∈ Set.range f := by
  constructor
  · intro ⟨b, hb⟩
    have h (n : ℕ) :
        ∃ a : ℕ → ℕ, (∀ i (hi : i < n), b i = a i) ∧
          dist x (f a) < (1 / 2 : ℝ) ^ n := by
      let s := List.ofFn (fun i : Fin n => b i)
      have hs : s ∈ (approximationTree f x).val := hb n
      obtain ⟨a, ha, hdist⟩ := hs
      refine ⟨a, ?_, by simpa [s] using hdist⟩
      intro i hi
      have hi' : i < s.length := by simpa [s] using hi
      simpa [s] using ha i hi'
    choose a hagrees hdist using h
    have hat : Tendsto a atTop (𝓝 b) := tendsto_pi_nhds.mpr fun i => by
      have he : (fun _ : ℕ => b i) =ᶠ[atTop] (fun n => a n i) :=
        (eventually_ge_atTop (i + 1)).mono fun n hn => hagrees n i (by omega)
      exact tendsto_const_nhds.congr' he
    have hzero : Tendsto (fun n => dist (f (a n)) x) atTop (𝓝 0) :=
      squeeze_zero (fun _ => dist_nonneg)
        (fun n => (dist_comm (f (a n)) x).le.trans (hdist n).le)
        (show Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) from
          tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    exact ⟨b, tendsto_nhds_unique ((hf.tendsto b).comp hat)
      (tendsto_iff_dist_tendsto_zero.mpr hzero)⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, fun n => ⟨b, fun i hi => by simp,
      by simp⟩⟩

section Completeness

open MeasureTheory TopologicalSpace

theorem analyticSet_reduces_illFounded {Y : Type*} [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {A : Set Y} (hA : AnalyticSet A) :
    ∃ f : Y → NatTree, Measurable f ∧ f ⁻¹' {T : NatTree | T.IsIllFounded} = A := by
  let _ := upgradeIsCompletelyMetrizable Y
  rw [AnalyticSet] at hA
  rcases hA with h | ⟨f, hf, hr⟩
  · subst A
    let T : NatTree := ⟨∅, fun _ _ _ h => False.elim h⟩
    refine ⟨fun _ => T, measurable_const, ?_⟩
    exact Set.ext fun _ => ⟨fun ⟨_, hb⟩ => hb 0, False.elim⟩
  · subst A
    exact ⟨approximationTree f, measurable_approximationTree f,
      Set.ext fun y => approximationTree_illFounded_iff hf y⟩

/-- Every analytic image in a standard Borel space Borel-reduces to ill-foundedness. -/
theorem analyticImage_reduces_illFounded {Y Z : Type*} [MeasurableSpace Y]
    [StandardBorelSpace Y] [MeasurableSpace Z] [StandardBorelSpace Z] {g : Z → Y}
    {B : Set Z} (hg : Measurable g) (hB : MeasurableSet B) :
    ∃ f : Y → NatTree, Measurable f ∧ f ⁻¹' {T : NatTree | T.IsIllFounded} = g '' B := by
  let _ := upgradeStandardBorel Y
  exact analyticSet_reduces_illFounded (hB.analyticSet_image hg)

theorem wellFounded_eq_compl_illFounded :
    {T : NatTree | T.IsWellFounded} = {T : NatTree | T.IsIllFounded}ᶜ :=
  Set.ext fun _ => Set.not_nonempty_iff_eq_empty.symm

theorem analyticSet_compl_wellFounded : AnalyticSet ({T : NatTree | T.IsWellFounded}ᶜ) := by
  rw [wellFounded_eq_compl_illFounded, compl_compl]
  exact analyticSet_illFounded

/-- A complement of an analytic image Borel-reduces to well-foundedness. -/
theorem compl_analyticImage_reduces_wellFounded {Y Z : Type*} [MeasurableSpace Y]
    [StandardBorelSpace Y] [MeasurableSpace Z] [StandardBorelSpace Z] {g : Z → Y}
    {B : Set Z} (hg : Measurable g) (hB : MeasurableSet B) :
    ∃ f : Y → NatTree, Measurable f ∧ f ⁻¹' {T : NatTree | T.IsWellFounded} = (g '' B)ᶜ := by
  obtain ⟨f, hf, h⟩ := analyticImage_reduces_illFounded hg hB
  exact ⟨f, hf, by rw [wellFounded_eq_compl_illFounded, Set.preimage_compl, h]⟩

end Completeness
section Universal

local notation "Baire" => (ℕ → ℕ)

/-- Pair the coordinates of two branches into one branch. -/
def pairedBranch (x y : Baire) : Baire :=
  fun n => Nat.pair (x n) (y n)

theorem continuous_pairedBranch : Continuous (fun p : Baire × Baire => pairedBranch p.1 p.2) :=
  continuous_pi fun n =>
    (continuous_of_discreteTopology : Continuous (Function.uncurry Nat.pair)).comp
      (show Continuous (fun p : Baire × Baire => (p.1 n, p.2 n)) from
        ((continuous_apply n).comp continuous_fst).prodMk
          ((continuous_apply n).comp continuous_snd))

/-- The tree of finite paired prefixes realized by a relation on Baire space. -/
def treeOfRelation (R : Set (Baire × Baire)) : NatTree :=
  ⟨{s | ∃ p ∈ R, ∀ i (hi : i < s.length), s[i] = pairedBranch p.1 p.2 i},
    fun s t hst ⟨p, hp, h⟩ => ⟨p, hp, fun i hi =>
      (hst.getElem hi).trans (h i (hi.trans_le hst.length_le))⟩⟩

theorem pairedBranch_mem_treeOfRelation_iff {R : Set (Baire × Baire)} (hR : IsClosed R)
    (x y : Baire) : pairedBranch x y ∈ (treeOfRelation R).branches ↔ (x, y) ∈ R := by
  constructor
  · intro h
    have hs (n : ℕ) :
        ∃ p ∈ R, ∀ i (hi : i < n), pairedBranch x y i = pairedBranch p.1 p.2 i := by
      let s := List.ofFn (fun i : Fin n => pairedBranch x y i)
      have hm : s ∈ (treeOfRelation R).val := h n
      obtain ⟨p, hp, hp'⟩ := hm
      refine ⟨p, hp, fun i hi => ?_⟩
      have hi' : i < s.length := by simpa [s] using hi
      simpa [s] using hp' i hi'
    choose p hp hprefix using hs
    have ht₁ : Tendsto (fun n => (p n).1) atTop (𝓝 x) := tendsto_pi_nhds.mpr fun i =>
      tendsto_const_nhds.congr' ((eventually_ge_atTop (i + 1)).mono fun n hn =>
        (Nat.pair_eq_pair.mp (hprefix n i (by omega))).1)
    have ht₂ : Tendsto (fun n => (p n).2) atTop (𝓝 y) := tendsto_pi_nhds.mpr fun i =>
      tendsto_const_nhds.congr' ((eventually_ge_atTop (i + 1)).mono fun n hn =>
        (Nat.pair_eq_pair.mp (hprefix n i (by omega))).2)
    exact hR.mem_of_tendsto (ht₁.prodMk_nhds ht₂) (Eventually.of_forall hp)
  · intro h
    exact fun n => ⟨(x, y), h, fun i hi => by simp⟩

/-- The sections of this set by tree parameters are all analytic subsets of Baire space. -/
def treeSections : Set (NatTree × Baire) :=
  {p | ∃ y : Baire, pairedBranch p.2 y ∈ p.1.branches}

theorem analyticSet_treeSections : MeasureTheory.AnalyticSet treeSections := by
  let _ := TopologicalSpace.upgradeIsCompletelyMetrizable NatTree
  let _ : MetricSpace Baire := PiNat.metricSpaceNatNat
  let f (p : (NatTree × Baire) × Baire) := (p.1.1, pairedBranch p.1.2 p.2)
  have hf : Continuous f :=
    (continuous_fst.comp continuous_fst).prodMk
      (continuous_pairedBranch.comp
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
  have hc := isClosed_branchRelation.preimage hf
  have hproj : Prod.fst '' (f ⁻¹' {p : NatTree × Baire | p.2 ∈ p.1.branches}) = treeSections :=
    Set.ext fun p => by simp [treeSections, f]
  exact hproj ▸ hc.analyticSet.image_of_continuous continuous_fst

theorem exists_treeSection_eq (A : Set Baire) (hA : MeasureTheory.AnalyticSet A) :
    ∃ T : NatTree, {x : Baire | (T, x) ∈ treeSections} = A := by
  rw [MeasureTheory.AnalyticSet] at hA
  rcases hA with h | ⟨f, hf, hr⟩
  · subst A
    refine ⟨treeOfRelation ∅, Set.ext fun _ => ?_⟩
    simp [treeSections, pairedBranch_mem_treeOfRelation_iff isClosed_empty]
  · subst A
    let R : Set (Baire × Baire) := {p | f p.2 = p.1}
    have hR : IsClosed R := isClosed_eq (hf.comp continuous_snd) continuous_fst
    refine ⟨treeOfRelation R, Set.ext fun _ => ?_⟩
    simp [treeSections, pairedBranch_mem_treeOfRelation_iff hR, R]

/-- Diagonalization of the universal analytic family gives a non-analytic coanalytic set. -/
theorem exists_coanalytic_not_analytic_baire :
    ∃ D : Set Baire, MeasureTheory.AnalyticSet (Dᶜ) ∧ ¬ MeasureTheory.AnalyticSet D := by
  let _ : Nonempty NatTree := ⟨⟨∅, fun _ _ _ h => False.elim h⟩⟩
  let _ : MetricSpace Baire := PiNat.metricSpaceNatNat
  obtain ⟨g, hg, hgs⟩ := PolishSpace.exists_nat_nat_continuous_surjective NatTree
  let f (b : Baire) := (g b, b)
  let D := (f ⁻¹' treeSections)ᶜ
  refine ⟨D, ?_, ?_⟩
  · change MeasureTheory.AnalyticSet ((f ⁻¹' treeSections)ᶜ)ᶜ
    rw [compl_compl]
    exact analyticSet_treeSections.preimage (hg.prodMk continuous_id)
  · intro hD
    obtain ⟨T, hT⟩ := exists_treeSection_eq D hD
    obtain ⟨b, hb⟩ := hgs T
    have he : (T, b) ∈ treeSections ↔ b ∈ D := by
      change b ∈ {x : Baire | (T, x) ∈ treeSections} ↔ b ∈ D
      rw [hT]
    have hc : b ∈ D ↔ (T, b) ∉ treeSections := by
      change (g b, b) ∉ treeSections ↔ (T, b) ∉ treeSections
      rw [hb]
    by_cases hs : (T, b) ∈ treeSections
    · exact (hc.mp (he.mp hs)) hs
    · exact hs (he.mpr (hc.mpr hs))

theorem not_analyticSet_wellFounded :
    ¬ MeasureTheory.AnalyticSet {T : NatTree | T.IsWellFounded} := by
  let _ : MetricSpace Baire := PiNat.metricSpaceNatNat
  let _ : MeasurableSpace Baire := borel Baire
  let _ : BorelSpace Baire := ⟨rfl⟩
  intro hW
  obtain ⟨D, hDc, hD⟩ := exists_coanalytic_not_analytic_baire
  obtain ⟨f, hf, h⟩ := analyticSet_reduces_illFounded hDc
  have he : f ⁻¹' {T : NatTree | T.IsWellFounded} = D := by
    rw [wellFounded_eq_compl_illFounded, Set.preimage_compl, h, compl_compl]
  exact hD (he ▸ analyticSet_preimage_measurable hf hW)

end Universal
end PaperFormalization.NatTree
