import PaperFormalization.EffrosEquality

namespace PaperFormalization

open Filter Set Topology TopologicalSpace

section Selection

variable {A X : Type*} [MeasurableSpace A] [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable (F : A → Set X) (hF : ∀ U : Set X, IsOpen U →
  MeasurableSet {a | (F a ∩ U).Nonempty})

include hF
omit [MeasurableSpace X] [BorelSpace X] in
theorem measurable_infDist_family (h₀ : ∀ a, (F a).Nonempty) (x : X) :
    Measurable (fun a => Metric.infDist x (F a)) := by
  apply measurable_of_Iio
  intro r
  have h : (fun a => Metric.infDist x (F a)) ⁻¹' Iio r =
      {a | (F a ∩ Metric.ball x r).Nonempty} := Set.ext fun a =>
    (Metric.infDist_lt_iff (h₀ a)).trans
      ⟨fun ⟨y, hy, hd⟩ => ⟨y, hy, by simpa [Metric.mem_ball, dist_comm] using hd⟩,
       fun ⟨y, hy, hd⟩ => ⟨y, hy, by simpa [Metric.mem_ball, dist_comm] using hd⟩⟩
  rw [h]
  exact hF _ Metric.isOpen_ball

variable [SeparableSpace X] [Nonempty X]

theorem measurable_infDist_family_apply (h₀ : ∀ a, (F a).Nonempty) :
    Measurable (fun p : A × X => Metric.infDist p.2 (F p.1)) := by
  let d := denseSeq X
  apply measurable_of_Iio
  intro r
  have he : (fun p : A × X => Metric.infDist p.2 (F p.1)) ⁻¹' Iio r =
      ⋃ k : ℕ, ⋃ q : ℚ, (Prod.fst ⁻¹' {a | (F a ∩ Metric.ball (d k) q).Nonempty}) ∩
        Prod.snd ⁻¹' {x | dist x (d k) + (q : ℝ) < r} := by
    ext p
    constructor
    · intro hp
      obtain ⟨y, hy, hy'⟩ := (Metric.infDist_lt_iff (h₀ p.1)).mp hp
      let ε := (r - dist p.2 y) / 3
      have hε : 0 < ε := by dsimp [ε]; linarith
      obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp (denseRange_denseSeq X) y ε hε
      have hk' : dist p.2 (d k) ≤ dist p.2 y + dist y (d k) := dist_triangle _ _ _
      have hgap : dist y (d k) < r - dist p.2 (d k) := by dsimp [ε] at hk; linarith
      obtain ⟨q, hq, hq'⟩ := exists_rat_btwn hgap
      exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨q, ⟨⟨y, hy, hq⟩, by
        change dist p.2 (d k) + (q : ℝ) < r
        linarith⟩⟩⟩
    · intro hp
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hp
      obtain ⟨q, ⟨⟨y, hy, hdy⟩, hdist⟩⟩ := Set.mem_iUnion.mp hk
      change dist y (d k) < (q : ℝ) at hdy
      change dist p.2 (d k) + (q : ℝ) < r at hdist
      exact (Metric.infDist_lt_iff (h₀ p.1)).mpr ⟨y, hy, by
        have ht := dist_triangle p.2 (d k) y
        rw [dist_comm (d k) y] at ht
        linarith⟩
  rw [he]
  exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun q =>
    (measurable_fst (hF _ Metric.isOpen_ball)).inter
      (measurable_snd ((isOpen_lt ((continuous_id.dist continuous_const).add continuous_const)
        continuous_const).measurableSet))

omit [Nonempty X] in
theorem exists_selectorStep (h₀ : ∀ a, (F a).Nonempty) (d : ℕ → X) (hd : DenseRange d)
    (r s : ℝ) (hs : 0 < s) (k : A → ℕ) (hk : Measurable k)
    (hnear : ∀ a, Metric.infDist (d (k a)) (F a) < r) :
    ∃ l : A → ℕ, Measurable l ∧ ∀ a,
      Metric.infDist (d (l a)) (F a) < s ∧ dist (d (k a)) (d (l a)) < r + s := by
  classical
  let P (a : A) (j : ℕ) :=
    Metric.infDist (d j) (F a) < s ∧ dist (d (k a)) (d j) < r + s
  have h (a : A) : ∃ j, P a j := by
    obtain ⟨y, hy, hy'⟩ := (Metric.infDist_lt_iff (h₀ a)).mp (hnear a)
    obtain ⟨j, hj⟩ := Metric.denseRange_iff.mp hd y s hs
    exact ⟨j, (Metric.infDist_le_dist_of_mem hy).trans_lt ((dist_comm _ _).le.trans_lt hj),
      (dist_triangle _ y _).trans_lt (add_lt_add hy' hj)⟩
  refine ⟨fun a => Nat.find (h a), measurable_find h ?_, fun a => Nat.find_spec (h a)⟩
  intro j
  exact (measurableSet_lt (measurable_infDist_family F hF h₀ (d j)) measurable_const).inter
    (measurableSet_lt (((measurable_of_countable d).comp hk).dist measurable_const) measurable_const)

/-- A measurable choice of centers close to the fibers can be refined into an actual selector. -/
theorem exists_measurable_selector_near [CompleteSpace X]
    (h₀ : ∀ a, (F a).Nonempty) (hclosed : ∀ a, IsClosed (F a)) {r : ℝ} (hr : 0 < r)
    (k : A → ℕ) (hk : Measurable k)
    (hnear : ∀ a, Metric.infDist (denseSeq X (k a)) (F a) < r) :
    ∃ g : A → X, Measurable g ∧ ∀ a, g a ∈ F a ∧ dist (denseSeq X (k a)) (g a) ≤ 4 * r := by
  let d := denseSeq X
  let R (n : ℕ) := r / (2 : ℝ) ^ n
  have hR (n : ℕ) : 0 < R n := by dsimp [R]; positivity
  let Stage (n : ℕ) := {k : A → ℕ // Measurable k ∧
    ∀ a, Metric.infDist (d (k a)) (F a) < R n}
  have next (n : ℕ) (z : Stage n) : ∃ w : Stage (n + 1),
      ∀ a, dist (d (z.val a)) (d (w.val a)) < R n + R (n + 1) := by
    obtain ⟨w, hw, hw'⟩ := exists_selectorStep F hF h₀ d (denseRange_denseSeq X)
      (R n) (R (n + 1)) (hR _) z.val z.property.1 z.property.2
    exact ⟨⟨w, hw, fun a => (hw' a).1⟩, fun a => (hw' a).2⟩
  let u : (n : ℕ) → Stage n := Nat.rec
    ⟨k, hk, by simpa [R] using hnear⟩ (fun n z => Classical.choose (next n z))
  let c (n : ℕ) (a : A) := d ((u n).val a)
  have hstep (a : A) (n : ℕ) :
      dist (c n a) (c (n + 1) a) ≤ (4 * r) / 2 / 2 ^ n := by
    have he := (Classical.choose_spec (next n (u n)) a).le
    change dist (c n a) (c (n + 1) a) ≤ R n + R (n + 1) at he
    refine he.trans ?_
    dsimp [R]
    rw [pow_succ]
    have hp : 0 < (2 : ℝ) ^ n := by positivity
    field_simp
    linarith
  have hconv (a : A) : ∃ x, Tendsto (fun n => c n a) atTop (𝓝 x) :=
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two (hstep a))
  choose g hg using hconv
  refine ⟨g, measurable_of_tendsto_metrizable
    (fun n => (measurable_of_countable d).comp (u n).property.1)
    (tendsto_pi_nhds.mpr hg), fun a => ⟨?_,
      dist_le_of_le_geometric_two_of_tendsto₀ (hstep a) (hg a)⟩⟩
  apply ((hclosed a).mem_iff_infDist_zero (h₀ a)).mpr
  have hlim := ((Metric.continuous_infDist_pt (F a)).tendsto (g a)).comp (hg a)
  have hzero : Tendsto (fun n => Metric.infDist (c n a) (F a)) atTop (𝓝 0) :=
    squeeze_zero (fun _ => Metric.infDist_nonneg) (fun n => ((u n).property.2 a).le)
      (by
        simpa [R, div_eq_mul_inv, inv_pow] using
          (tendsto_pow_atTop_nhds_zero_of_lt_one
            (by norm_num : 0 ≤ (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul r)
  exact tendsto_nhds_unique hlim hzero

/-- A hit-measurable family of nonempty closed sets admits measurable dense selectors. -/
theorem exists_measurable_dense_selectors [CompleteSpace X]
    (h₀ : ∀ a, (F a).Nonempty) (hclosed : ∀ a, IsClosed (F a)) :
    ∃ g : ℕ → A → X, (∀ n, Measurable (g n)) ∧
      ∀ a, closure (Set.range fun n => g n a) = F a := by
  classical
  let d := denseSeq X
  let R (n : ℕ) := (1 / 2 : ℝ) ^ n
  have hR (n : ℕ) : 0 < R n := pow_pos (by norm_num) _
  have hex (n : ℕ) (a : A) : ∃ j, Metric.infDist (d j) (F a) < R n := by
    obtain ⟨y, hy⟩ := h₀ a
    obtain ⟨j, hj⟩ := Metric.denseRange_iff.mp (denseRange_denseSeq X) y _ (hR n)
    exact ⟨j, (Metric.infDist_le_dist_of_mem hy).trans_lt ((dist_comm _ _).le.trans_lt hj)⟩
  have hsel (n j : ℕ) : ∃ g : A → X, Measurable g ∧
      ∀ a, g a ∈ F a ∧ (Metric.infDist (d j) (F a) < R n → dist (d j) (g a) ≤ 4 * R n) := by
    let k (a : A) := if Metric.infDist (d j) (F a) < R n then j else Nat.find (hex n a)
    have hk : Measurable k := Measurable.ite
      (measurableSet_lt (measurable_infDist_family F hF h₀ _) measurable_const)
      measurable_const
      (measurable_find (hex n) fun _ =>
        measurableSet_lt (measurable_infDist_family F hF h₀ _) measurable_const)
    have hkn (a : A) : Metric.infDist (d (k a)) (F a) < R n := by
      by_cases h : Metric.infDist (d j) (F a) < R n
      · simpa only [k, if_pos h] using h
      · simpa only [k, if_neg h] using Nat.find_spec (hex n a)
    obtain ⟨g, hg, hg'⟩ := exists_measurable_selector_near F hF h₀ hclosed (hR n) k hk hkn
    exact ⟨g, hg, fun a => ⟨(hg' a).1, fun h => by
      simpa only [d, k, if_pos h] using (hg' a).2⟩⟩
  choose g hg hg' using hsel
  let f (n : ℕ) := g (Nat.unpair n).1 (Nat.unpair n).2
  refine ⟨f, fun n => hg _ _, fun a => le_antisymm ?_ ?_⟩
  · exact closure_minimal (Set.range_subset_iff.mpr fun n => (hg' _ _ a).1) (hclosed a)
  · intro x hx
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 5 by positivity)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    obtain ⟨j, hj⟩ := Metric.denseRange_iff.mp (denseRange_denseSeq X) x _ (hR n)
    have hnear : Metric.infDist (d j) (F a) < R n :=
      (Metric.infDist_le_dist_of_mem hx).trans_lt ((dist_comm _ _).le.trans_lt hj)
    refine ⟨g n j a, ⟨Nat.pair n j, by simp [f]⟩, ?_⟩
    have ht := dist_triangle x (d j) (g n j a)
    have hgj := (hg' n j a).2 hnear
    change R n < ε / 5 at hn
    change dist x (d j) < R n at hj
    linarith

end Selection
namespace ClosedSubspaces

theorem exists_borel_dense_selectors {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [SeparableSpace E] [MeasurableSpace E] [BorelSpace E] :
    ∃ g : ℕ → ClosedSubspaces E → E, (∀ n, Measurable (g n)) ∧
      ∀ W, closure (Set.range fun n => g n W) = W.val :=
  exists_measurable_dense_selectors (fun W : ClosedSubspaces E => (W.val : Set E))
    (fun _ hU => measurableSet_hit (E := E) hU) (fun W => ⟨0, W.val.zero_mem⟩) Subtype.property

theorem measurableSet_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SeparableSpace E] [MeasurableSpace E] [BorelSpace E] :
    MeasurableSet {p : ClosedSubspaces E × E | p.2 ∈ p.1.val} := by
  have he : {p : ClosedSubspaces E × E | p.2 ∈ p.1.val} =
      {p : ClosedSubspaces E × E | Metric.infDist p.2 (p.1.val : Set E) = 0} :=
    Set.ext fun p => p.1.property.mem_iff_infDist_zero ⟨0, p.1.val.zero_mem⟩
  rw [he]
  have hd : Measurable (fun p : ClosedSubspaces E × E => Metric.infDist p.2 (p.1.val : Set E)) :=
    measurable_infDist_family_apply (fun W : ClosedSubspaces E => (W.val : Set E))
      (fun _ hU => measurableSet_hit (E := E) hU) (fun W => ⟨0, W.val.zero_mem⟩)
  exact measurableSet_eq_fun hd measurable_const

theorem measurableSet_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [SeparableSpace E] [MeasurableSpace E] [BorelSpace E] :
    MeasurableSet {p : ClosedSubspaces E × ClosedSubspaces E | p.1.val ≤ p.2.val} := by
  obtain ⟨g, hg, hclosure⟩ := exists_borel_dense_selectors (E := E)
  have h : {p : ClosedSubspaces E × ClosedSubspaces E | p.1.val ≤ p.2.val} =
      ⋂ n, {p : ClosedSubspaces E × ClosedSubspaces E | g n p.1 ∈ p.2.val} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hp n
      apply hp
      change g n p.1 ∈ (p.1.val : Set E)
      rw [← hclosure p.1]
      exact subset_closure (Set.mem_range_self n)
    · intro hp x hx
      change x ∈ (p.1.val : Set E) at hx
      rw [← hclosure p.1] at hx
      exact closure_minimal (Set.range_subset_iff.mpr hp) p.2.property hx
  rw [h]
  exact MeasurableSet.iInter fun n =>
    ((measurable_snd.prodMk ((hg n).comp measurable_fst)) (measurableSet_mem (E := E)))

end ClosedSubspaces
end PaperFormalization
