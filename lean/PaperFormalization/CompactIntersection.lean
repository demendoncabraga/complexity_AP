import PaperFormalization.EffrosSelectors
import Mathlib.Topology.MetricSpace.Closeds

namespace PaperFormalization

open Set Topology TopologicalSpace

/-- Intersecting a hit-measurable compact family with a hit-measurable closed family
preserves hit measurability. The closed fibers are assumed nonempty. -/
theorem measurableSet_hit_compact_inter_closed
    {A X : Type*} [MeasurableSpace A] [MetricSpace X] [SeparableSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (K F : A → Set X) (hKc : ∀ a, IsCompact (K a))
    (hFc : ∀ a, IsClosed (F a)) (hFn : ∀ a, (F a).Nonempty)
    (hK : ∃ k : ℕ → A → X, (∀ i, Measurable (k i)) ∧
      ∀ a, closure (range fun i => k i a) = K a)
    (hF : ∀ U : Set X, IsOpen U → MeasurableSet {a | (F a ∩ U).Nonempty})
    {U : Set X} (hU : IsOpen U) :
    MeasurableSet {a | ((K a ∩ F a) ∩ U).Nonempty} := by
  obtain ⟨k, hk, hk'⟩ := hK
  let d := denseSeq X
  let P (j : ℕ) (q : ℚ) (n i : ℕ) :=
    {a | k i a ∈ Metric.ball (d j) q ∧ Metric.infDist (k i a) (F a) < (1 : ℝ) / (n + 1)}
  have hd := measurable_infDist_family_apply F hF hFn
  have hP (j : ℕ) (q : ℚ) (n i : ℕ) : MeasurableSet (P j q n i) :=
    (hk i Metric.isOpen_ball.measurableSet).inter
      (measurableSet_lt (hd.comp (measurable_id.prodMk (hk i))) measurable_const)
  let J := {p : ℕ × ℚ | Metric.closedBall (d p.1) p.2 ⊆ U}
  have he : {a | ((K a ∩ F a) ∩ U).Nonempty} =
      ⋃ p : J, ⋂ n, ⋃ i, P p.val.1 p.val.2 n i := by
    ext a
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter]
    constructor
    · rintro ⟨x, ⟨hxK, hxF⟩, hxU⟩
      obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_ball.mem_iff.mp (hU.mem_nhds hxU)
      obtain ⟨j, hj⟩ := Metric.denseRange_iff.mp (denseRange_denseSeq X) x (r / 3) (by positivity)
      change dist x (d j) < r / 3 at hj
      obtain ⟨q, hq, hq'⟩ := exists_rat_btwn (show dist x (d j) < r - dist x (d j) by linarith)
      have hsub : Metric.closedBall (d j) q ⊆ U := by
        intro y hy
        apply hrU
        have ht := dist_triangle y (d j) x
        rw [dist_comm (d j) x] at ht
        change dist y (d j) ≤ (q : ℝ) at hy
        change dist y x < r
        linarith
      refine ⟨⟨(j, q), hsub⟩, fun n => ?_⟩
      let V := Metric.ball (d j) q ∩ {y | Metric.infDist y (F a) < (1 : ℝ) / (n + 1)}
      have hV : IsOpen V := Metric.isOpen_ball.inter
        (isOpen_lt (Metric.continuous_infDist_pt _) continuous_const)
      have hxV : x ∈ V := ⟨hq, by
        change Metric.infDist x (F a) < (1 : ℝ) / (n + 1)
        rw [Metric.infDist_zero_of_mem hxF]
        positivity⟩
      have hh : (closure (range fun i => k i a) ∩ V).Nonempty :=
        ⟨x, (hk' a).symm ▸ hxK, hxV⟩
      obtain ⟨_, ⟨i, rfl⟩, hi⟩ := (closure_inter_open_nonempty_iff hV).mp hh
      exact ⟨i, hi⟩
    · rintro ⟨p, hp⟩
      let C := K a ∩ Metric.closedBall (d p.val.1) p.val.2
      have hc (n : ℕ) : ∃ y ∈ C, Metric.infDist y (F a) < (1 : ℝ) / (n + 1) := by
        obtain ⟨i, hi, hi'⟩ := hp n
        exact ⟨k i a, ⟨hk' a ▸ subset_closure (mem_range_self i), Metric.ball_subset_closedBall hi⟩, hi'⟩
      obtain ⟨y, hy, hymin⟩ :=
        ((hKc a).inter_right Metric.isClosed_closedBall).exists_isMinOn
          (by obtain ⟨z, hz, _⟩ := hc 0; exact ⟨z, hz⟩)
          (Metric.continuous_infDist_pt (F a)).continuousOn
      have hyzero : Metric.infDist y (F a) = 0 := by
        apply le_antisymm _ Metric.infDist_nonneg
        by_contra! hpos
        obtain ⟨n, hn⟩ := exists_nat_gt ((Metric.infDist y (F a))⁻¹)
        obtain ⟨z, hz, hzd⟩ := hc n
        have hle := hymin hz
        have hsmall : (1 : ℝ) / (n + 1) < Metric.infDist y (F a) := by
          rw [one_div, inv_lt_comm₀ (by positivity) hpos]
          linarith
        exact ((hle.trans_lt hzd).trans hsmall).false
      exact ⟨y, ⟨hy.1, (hFc a).mem_iff_infDist_zero (hFn a) |>.mpr hyzero⟩, p.property hy.2⟩
  rw [he]
  exact MeasurableSet.iUnion fun p => MeasurableSet.iInter fun n =>
    MeasurableSet.iUnion fun i => hP p.val.1 p.val.2 n i

end PaperFormalization

namespace PaperFormalization

open Set Topology TopologicalSpace

section Compacts

variable {X : Type*} [MetricSpace X] [SeparableSpace X] [CompleteSpace X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X]

noncomputable local instance : MeasurableSpace (NonemptyCompacts X) :=
  borel (NonemptyCompacts X)

local instance : BorelSpace (NonemptyCompacts X) := ⟨rfl⟩

theorem exists_borel_compact_selectors :
    ∃ k : ℕ → NonemptyCompacts X → X, (∀ i, Measurable (k i)) ∧
      ∀ K, closure (range fun i => k i K) = (K : Set X) :=
  exists_measurable_dense_selectors (fun K : NonemptyCompacts X => (K : Set X))
    (fun _ hU => (NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU).measurableSet)
    (fun K => K.nonempty) (fun K => K.isCompact.isClosed)

end Compacts

abbrev CompactsContainingZero (E : Type*) [TopologicalSpace E] [Zero E] :=
  {K : NonemptyCompacts E // (0 : E) ∈ (K : Set E)}

section CompactSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [SeparableSpace E] [MeasurableSpace E] [BorelSpace E]

noncomputable instance : MeasurableSpace (CompactsContainingZero E) :=
  letI : MeasurableSpace (NonemptyCompacts E) := borel (NonemptyCompacts E)
  inferInstanceAs (MeasurableSpace {K : NonemptyCompacts E // (0 : E) ∈ (K : Set E)})

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem compactsContainingZero_standardBorel : StandardBorelSpace (CompactsContainingZero E) := by
  let : MeasurableSpace (NonemptyCompacts E) := borel (NonemptyCompacts E)
  have : BorelSpace (NonemptyCompacts E) := ⟨rfl⟩
  have h : IsClosed {K : NonemptyCompacts E | (0 : E) ∈ (K : Set E)} := by
    simpa only [inter_singleton_nonempty] using
      (NonemptyCompacts.isClosed_inter_nonempty_of_isClosed
        (isClosed_singleton (x := (0 : E))))
  exact h.measurableSet.standardBorel

theorem exists_borel_compactSubspace_intersection_selectors :
    ∃ s : ℕ → CompactsContainingZero E × ClosedSubspaces E → E,
      (∀ i, Measurable (s i)) ∧ ∀ p, closure (range fun i => s i p) =
        (p.1.val : Set E) ∩ (p.2.val : Set E) := by
  let : MeasurableSpace (NonemptyCompacts E) := borel (NonemptyCompacts E)
  let K (p : CompactsContainingZero E × ClosedSubspaces E) := (p.1.val : Set E)
  let F (p : CompactsContainingZero E × ClosedSubspaces E) := (p.2.val : Set E)
  have hK := exists_borel_compact_selectors (X := E)
  obtain ⟨k, hk, hk'⟩ := hK
  have hg : Measurable (fun p : CompactsContainingZero E × ClosedSubspaces E => p.1.val) := by
    exact measurable_subtype_coe.comp measurable_fst
  have hselectors : ∃ k' : ℕ → CompactsContainingZero E × ClosedSubspaces E → E,
      (∀ i, Measurable (k' i)) ∧ ∀ p, closure (range fun i => k' i p) = K p :=
    ⟨fun i p => k i p.1.val, fun i => (hk i).comp hg, fun p => hk' p.1.val⟩
  exact exists_measurable_dense_selectors (fun p => K p ∩ F p)
    (fun _ hU => measurableSet_hit_compact_inter_closed K F
      (fun p => p.1.val.isCompact) (fun p => p.2.property) (fun p => ⟨0, p.2.val.zero_mem⟩)
      hselectors (fun _ hV => measurable_snd (ClosedSubspaces.measurableSet_hit (E := E) hV)) hU)
    (fun p => ⟨0, p.1.property, p.2.val.zero_mem⟩)
    (fun p => p.1.val.isCompact.isClosed.inter p.2.property)

end CompactSubspace

end PaperFormalization
