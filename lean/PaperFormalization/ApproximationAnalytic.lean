import PaperFormalization.ComplementedAnalytic
import PaperFormalization.CompactIntersection
import Mathlib.Analysis.Normed.Module.HahnBanach

namespace PaperFormalization

open Set Topology TopologicalSpace MeasureTheory
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem continuous_weakStarUnitBall_eval :
    Continuous (fun p : WeakStarUnitBall E × E => p.1.val p.2) := by
  exact continuous_eval.comp
    ((weakStarBallLinearIsometry (E := E)).continuous.comp continuous_snd |>.prodMk continuous_fst)

private theorem exists_uniform_approx_weakStarUnitBall
    {K : Set E} (hK : IsCompact K) (f : ℕ → WeakStarUnitBall E) (hf : DenseRange f)
    (g : WeakStarUnitBall E) {ε : ℝ} (hε : 0 < ε) :
    ∃ n, ∀ x ∈ K, ‖(f n).val x - g.val x‖ < ε := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let eval (u : WeakStarUnitBall E) : C(K, ℝ) :=
    ⟨fun x => u.val x.val, u.val.toStrongDual.continuous.comp continuous_subtype_val⟩
  have hc : Continuous eval := ContinuousMap.continuous_of_continuous_uncurry eval
    (continuous_weakStarUnitBall_eval.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := (show Dense (range f) from hf).exists_mem_open
    ((Metric.isOpen_ball (x := eval g) (ε := ε)).preimage hc)
    ⟨g, Metric.mem_ball_self hε⟩
  refine ⟨n, fun x hx => ?_⟩
  have he := ContinuousMap.norm_coe_le_norm (eval (f n) - eval g) ⟨x, hx⟩
  exact he.trans_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hn)

private theorem finiteRank_decompose (T : E →L[ℝ] E)
    (hT : FiniteDimensional ℝ T.toLinearMap.range) :
    ∃ k : ℕ, ∃ v : Fin k → E, ∃ f : Fin k → StrongDual ℝ E,
      (∀ i, ‖f i‖ ≤ 1) ∧ ∀ x, T x = ∑ i, f i x • v i := by
  let R := T.toLinearMap.range
  let B := Module.finBasis ℝ R
  let coord (i : Fin (Module.finrank ℝ R)) : R →L[ℝ] ℝ :=
    ⟨B.coord i, (B.coord i).continuous_of_finiteDimensional⟩
  let f (i : Fin (Module.finrank ℝ R)) := (coord i).comp T.rangeRestrict
  let c (i : Fin (Module.finrank ℝ R)) := max 1 ‖f i‖
  have hc (i : Fin (Module.finrank ℝ R)) : 0 < c i := lt_of_lt_of_le zero_lt_one (le_max_left ..)
  refine ⟨_, fun i => c i • (B i).val, fun i => (c i)⁻¹ • f i, fun i => ?_, fun x => ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hc i).le)]
    exact (inv_mul_le_iff₀ (hc i)).mpr (by simp [c])
  · have hB := congrArg (fun z : R => z.val) (B.sum_repr (T.rangeRestrict x))
    change ((∑ i, B.repr (T.rangeRestrict x) i • B i : R) : E) = T x at hB
    rw [← hB]
    simp only [smul_apply, smul_smul, Submodule.coe_sum, Submodule.coe_smul]
    apply Finset.sum_congr rfl
    intro i _
    change (f i x) • (B i).val = ((c i)⁻¹ * f i x * c i) • (B i).val
    rw [mul_comm ((c i)⁻¹) (f i x), mul_assoc, inv_mul_cancel₀ (hc i).ne', mul_one]

private theorem finiteRank_sum_smulRight {k : ℕ} (f : Fin k → StrongDual ℝ E) (v : Fin k → E) :
    FiniteDimensional ℝ (∑ i, (f i).smulRight (v i)).toLinearMap.range := by
  let S := Submodule.span ℝ (range v)
  have : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (finite_range v)
  have hs : (∑ i, (f i).smulRight (v i)).toLinearMap.range ≤ S := by
    rintro _ ⟨x, rfl⟩
    change (∑ i, (f i).smulRight (v i)) x ∈ S
    simp only [sum_apply,
      ContinuousLinearMap.smulRight_apply]
    exact S.sum_mem fun i _ => S.smul_mem _ (Submodule.subset_span (mem_range_self i))
  exact FiniteDimensional.of_injective (Submodule.inclusion hs) (Submodule.inclusion_injective hs)


private theorem weakStarUnitBall.le_norm (g : WeakStarUnitBall E) (x : E) :
    ‖g.val x‖ ≤ ‖x‖ := by
  have hg := g.property
  change dist g.val.toStrongDual 0 ≤ 1 at hg
  rw [dist_zero_right] at hg
  exact one_mul ‖x‖ ▸ g.val.toStrongDual.le_of_opNorm_le hg x

private theorem exists_approx_rankOne
    {X : BanachCode} {K : Set BanachAmbient} (hK : IsCompact K)
    (d : ℕ → BanachAmbient) (hd : closure (range d) = (X.val : Set BanachAmbient))
    (f : ℕ → WeakStarUnitBall BanachAmbient) (hf : DenseRange f)
    (v : X.val) (g : StrongDual ℝ X.val) (hg : ‖g‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ n m, ∀ x : X.val, x.val ∈ K →
      ‖g x • v.val - (f m).val x.val • d n‖ ≤ ε := by
  obtain ⟨G, hG, hG_norm⟩ := exists_extension_norm_eq X.val g
  let u : WeakStarUnitBall BanachAmbient := ⟨G.toWeakDual, by
    simpa only [Set.mem_preimage, StrongDual.toStrongDual_toWeakDual,
      Metric.mem_closedBall, dist_zero_right, hG_norm] using hg⟩
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_le
  let δ := ε / (2 * (‖v.val‖ + R + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδmul : δ * (2 * (‖v.val‖ + R + 1)) = ε := div_mul_cancel₀ ε (by positivity)
  have hv : v.val ∈ closure (range d) := hd.symm ▸ v.property
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := Metric.mem_closure_iff.mp hv δ hδ
  obtain ⟨m, hm⟩ := exists_uniform_approx_weakStarUnitBall hK f hf u hδ
  refine ⟨n, m, fun x hx => ?_⟩
  have hdiff : ‖g x - (f m).val x.val‖ ≤ δ := by
    rw [norm_sub_rev, ← hG x]
    exact (hm x.val hx).le
  have hdn : ‖v.val - d n‖ ≤ δ := by simpa only [dist_eq_norm] using hn.le
  have hrepr : g x • v.val - (f m).val x.val • d n =
      (g x - (f m).val x.val) • v.val + (f m).val x.val • (v.val - d n) := by
    rw [sub_smul, smul_sub]
    abel
  rw [hrepr]
  calc
    _ ≤ ‖(g x - (f m).val x.val) • v.val‖ + ‖(f m).val x.val • (v.val - d n)‖ :=
      norm_add_le _ _
    _ ≤ δ * ‖v.val‖ + R * δ := by
      simp only [norm_smul]
      exact add_le_add (mul_le_mul_of_nonneg_right hdiff (norm_nonneg _))
        (mul_le_mul (weakStarUnitBall.le_norm _ _ |>.trans (hKR _ hx)) hdn
          (norm_nonneg _) hR.le)
    _ ≤ ε := by nlinarith [norm_nonneg v.val]

theorem hasApproximationProperty_iff_ambient_test (X : BanachCode)
    (d : ℕ → BanachAmbient) (hd : closure (range d) = (X.val : Set BanachAmbient))
    (f : ℕ → WeakStarUnitBall BanachAmbient) (hf : DenseRange f) :
    HasApproximationProperty X.val ↔
      ∀ q : ℚ, 0 < q → ∀ K : CompactsContainingZero BanachAmbient,
        ∃ k : ℕ, ∃ n m : Fin k → ℕ, ∀ x ∈ (K.val : Set BanachAmbient) ∩ (X.val : Set BanachAmbient),
          ‖x - ∑ i, (f (m i)).val x • d (n i)‖ ≤ (q : ℝ) := by
  constructor
  · intro h q hq K
    have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
    let Y : Set X.val := Subtype.val ⁻¹' (K.val : Set BanachAmbient)
    have hclosed : IsClosed ((X.val : Set BanachAmbient)) := X.property
    have hEmb : IsEmbedding (Subtype.val : X.val → BanachAmbient) := IsEmbedding.subtypeVal
    have hrange : range (Subtype.val : X.val → BanachAmbient) = (X.val : Set BanachAmbient) :=
      Set.ext fun x => ⟨fun ⟨z, hz⟩ => hz ▸ z.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
    have hY : IsCompact Y := hEmb.isInducing.isCompact_preimage
      (hrange.symm ▸ hclosed) K.val.isCompact
    obtain ⟨T, hT, hTK⟩ := h ((q : ℝ) / 2) (by positivity) Y hY
    obtain ⟨k, v, g, hg, hsum⟩ := finiteRank_decompose T hT
    have hsmall : 0 < (q : ℝ) / (2 * (k + 1)) := by positivity
    have hb (i : Fin k) := exists_approx_rankOne K.val.isCompact d hd f hf (v i) (g i) (hg i) hsmall
    choose n m hnm using hb
    refine ⟨k, n, m, fun x hx => ?_⟩
    let y : X.val := ⟨x, hx.2⟩
    have hy : y ∈ Y := hx.1
    have he : (T y).val = ∑ i, g i y • (v i).val := by
      rw [hsum y, Submodule.coe_sum]
      simp only [Submodule.coe_smul]
    have hT' : ‖x - (T y).val‖ ≤ (q : ℝ) / 2 := hTK y hy
    calc
      _ ≤ ‖x - (T y).val‖ + ‖(T y).val - ∑ i, (f (m i)).val x • d (n i)‖ := by simpa only [dist_eq_norm] using dist_triangle x (T y).val _
      _ ≤ (q : ℝ) / 2 + ∑ i : Fin k, ((q : ℝ) / (2 * (k + 1))) := by
        apply add_le_add hT'
        rw [he, ← Finset.sum_sub_distrib]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hnm i y hx.1)
      _ ≤ (q : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hprod : (k : ℝ) * ((q : ℝ) / (2 * (k + 1))) ≤ (q : ℝ) / 2 := by
          rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
          nlinarith
        linarith
  · intro h ε hε K hK
    obtain ⟨q, hq, hq'⟩ := exists_rat_btwn hε
    have hq₀ : 0 < q := by exact_mod_cast hq
    let L : CompactsContainingZero BanachAmbient :=
      ⟨⟨⟨insert 0 (Subtype.val '' K), (hK.image continuous_subtype_val).insert _⟩, ⟨0, mem_insert _ _⟩⟩,
        mem_insert _ _⟩
    obtain ⟨k, n, m, happ⟩ := h q hq₀ L
    let v (i : Fin k) : X.val := ⟨d (n i), show d (n i) ∈ (X.val : Set BanachAmbient) from
      hd ▸ subset_closure (mem_range_self (n i))⟩
    let g (i : Fin k) : StrongDual ℝ X.val :=
      (f (m i)).val.toStrongDual.comp X.val.subtypeL
    refine ⟨∑ i, (g i).smulRight (v i), finiteRank_sum_smulRight g v, fun x hx => ?_⟩
    have hxL : x.val ∈ (L.val : Set BanachAmbient) := mem_insert_of_mem _ (mem_image_of_mem _ hx)
    have hw := happ x.val ⟨hxL, x.property⟩
    change ‖(x - (∑ i, (g i).smulRight (v i)) x).val‖ ≤ ε
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, Submodule.coe_sub,
      Submodule.coe_sum, Submodule.coe_smul, g, v, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    exact hw.trans hq'.le


/-- The set of coded separable real Banach spaces with the approximation property. -/
def approximationPropertyClass : Set BanachCode := {X | HasApproximationProperty X.val}

/-- Proposition 2.2, expressed as analyticity of the complement of AP. -/
theorem analyticSet_not_hasApproximationProperty :
    @AnalyticSet BanachCode banachCodePolishTopology approximationPropertyClassᶜ := by
  let t := upgradeStandardBorel BanachCode
  let : TopologicalSpace BanachCode := banachCodePolishTopology
  have : PolishSpace BanachCode := t.toPolishSpace
  have : BorelSpace BanachCode := t.toBorelSpace
  have : StandardBorelSpace BanachCode := banachCode_standardBorel
  have : StandardBorelSpace (CompactsContainingZero BanachAmbient) :=
    compactsContainingZero_standardBorel
  obtain ⟨d, hd, hdense⟩ := ClosedSubspaces.exists_borel_dense_selectors (E := BanachAmbient)
  obtain ⟨s, hs, hsdense⟩ := exists_borel_compactSubspace_intersection_selectors (E := BanachAmbient)
  obtain ⟨f, hf⟩ := exists_weakStarUnitBall_denseSeq (E := BanachAmbient)
  let P := CompactsContainingZero BanachAmbient × BanachCode
  let Q := {q : ℚ // 0 < q}
  let bound (k : ℕ) (n m : Fin k → ℕ) (X : BanachCode) (x : BanachAmbient) :=
    ‖x - ∑ i, (f (m i)).val x • d (n i) X‖
  let S : Set P := ⋂ q : Q, ⋃ k : ℕ, ⋃ n : Fin k → ℕ, ⋃ m : Fin k → ℕ, ⋂ j : ℕ,
    {p : P | bound k n m p.2 (s j p) ≤ (q.val : ℝ)}
  have hS : MeasurableSet S := by
    apply MeasurableSet.iInter
    intro q
    apply MeasurableSet.iUnion
    intro k
    apply MeasurableSet.iUnion
    intro n
    apply MeasurableSet.iUnion
    intro m
    apply MeasurableSet.iInter
    intro j
    apply measurableSet_le _ measurable_const
    have hterm (i : Fin k) : Measurable (fun p : P =>
        (f (m i)).val (s j p) • d (n i) p.2) :=
      ((f (m i)).val.toStrongDual.continuous.measurable.comp (hs j)).smul
        ((hd (n i)).comp measurable_snd)
    exact ((hs j).sub (Finset.measurable_sum Finset.univ fun i _ => hterm i)).norm
  have htest (p : P) (q : Q) (k : ℕ) (n m : Fin k → ℕ) :
      (∀ j, bound k n m p.2 (s j p) ≤ (q.val : ℝ)) ↔
        ∀ x ∈ (p.1.val : Set BanachAmbient) ∩ (p.2.val : Set BanachAmbient),
          bound k n m p.2 x ≤ (q.val : ℝ) := by
    constructor
    · intro h x hx
      apply closure_minimal (t := {y | bound k n m p.2 y ≤ (q.val : ℝ)})
        (range_subset_iff.mpr h) _ (hsdense p ▸ hx)
      refine isClosed_le ?_ continuous_const
      exact (continuous_id.sub (continuous_finsetSum _ fun i _ =>
        (f (m i)).val.toStrongDual.continuous.smul continuous_const)).norm
    · intro h j
      exact h _ (hsdense p ▸ subset_closure (mem_range_self j))
  have he (X : BanachCode) : HasApproximationProperty X.val ↔ ∀ K, (K, X) ∈ S := by
    rw [hasApproximationProperty_iff_ambient_test X (fun i => d i X) (hdense X) f hf]
    constructor
    · intro h K
      simp only [S, mem_iInter, mem_iUnion]
      intro q
      obtain ⟨k, n, m, hkm⟩ := h q.val q.property K
      exact ⟨k, n, m, (htest (K, X) q k n m).mpr hkm⟩
    · intro h q hq K
      have hK := h K
      simp only [S, mem_iInter, mem_iUnion] at hK
      obtain ⟨k, n, m, hkm⟩ := hK ⟨q, hq⟩
      exact ⟨k, n, m, (htest (K, X) ⟨q, hq⟩ k n m).mp hkm⟩
  have heq : Prod.snd '' Sᶜ = approximationPropertyClassᶜ := by
    ext X
    simp [approximationPropertyClass, he, P]
  rw [← heq]
  exact hS.compl.analyticSet_image measurable_snd

end PaperFormalization
