import PaperFormalization.CompactIntersection

namespace PaperFormalization

open Set Topology TopologicalSpace

private theorem not_nonempty_inter_compl_iff_subset {X : Type*} {S U : Set X} :
    ¬ (S ∩ Uᶜ).Nonempty ↔ S ⊆ U := by
  classical
  exact ⟨fun h x hx => by_contra fun hn => h ⟨x, hx, hn⟩,
    fun h ⟨x, hx, hn⟩ => hn (h hx)⟩

namespace EffrosClosed

variable {X : Type*} [TopologicalSpace X]

/-- The Effros generator consisting of the closed sets that intersect an open set. -/
def hit (U : Set X) : Set (Closeds X) := {F | ((F : Set X) ∩ U).Nonempty}

instance measurableSpace : MeasurableSpace (Closeds X) :=
  MeasurableSpace.generateFrom {S | ∃ U : Set X, IsOpen U ∧ S = hit U}

theorem measurableSet_hit {U : Set X} (hU : IsOpen U) : MeasurableSet (hit U) :=
  MeasurableSpace.measurableSet_generateFrom ⟨U, hU, rfl⟩

private def fromCode (p : Bool × (ℕ → X)) : Closeds X :=
  if p.1 then ⟨closure (range p.2), isClosed_closure⟩ else ⊥

private theorem measurable_fromCode [MeasurableSpace X] [OpensMeasurableSpace X] :
    Measurable (fromCode (X := X)) := by
  apply measurable_generateFrom
  rintro _ ⟨U, hU, rfl⟩
  have he : fromCode (X := X) ⁻¹' hit U =
      (Prod.fst ⁻¹' {true}) ∩ ⋃ n : ℕ, {p : Bool × (ℕ → X) | p.2 n ∈ U} := by
    ext p
    rcases p with ⟨b, s⟩
    cases b with
    | false =>
      simp [fromCode, hit, show ((⊥ : Closeds X) : Set X) = ∅ from rfl]
    | true =>
      change (closure (range s) ∩ U).Nonempty ↔ _
      rw [closure_inter_open_nonempty_iff hU]
      simp [Set.inter_nonempty]
  rw [he]
  exact (measurable_fst (measurableSet_singleton _)).inter (MeasurableSet.iUnion fun n =>
    ((measurable_pi_apply n).comp measurable_snd) hU.measurableSet)

end EffrosClosed

/-- A measurable space is standard Borel exactly when it has a compatible Polish topology. -/
theorem standardBorelSpace_iff_polish {X : Type*} [m : MeasurableSpace X] :
    StandardBorelSpace X ↔ ∃ t : TopologicalSpace X, @BorelSpace X t m ∧ @PolishSpace X t :=
  ⟨fun h => h.polish, fun h => ⟨h⟩⟩

theorem standardBorel_of_measurable_leftInverse {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [StandardBorelSpace B]
    {f : A → B} {g : B → A} (hf : Measurable f) (hg : Measurable g)
    (hgf : Function.LeftInverse g f) : StandardBorelSpace A := by
  let S := {b | f (g b) = b}
  have hS : MeasurableSet S := measurableSet_eq_fun (hf.comp hg) measurable_id
  have := hS.standardBorel
  have hmem (a : A) : f a ∈ S := congrArg f (hgf a)
  let e : A ≃ᵐ S :=
    { toFun := fun a => ⟨f a, hmem a⟩
      invFun := fun b => g b.val
      left_inv := hgf
      right_inv := fun b => Subtype.ext b.property
      measurable_toFun := hf.subtype_mk (h := hmem)
      measurable_invFun := hg.comp measurable_subtype_coe }
  let up := upgradeStandardBorel S
  let t := TopologicalSpace.induced e up.toTopologicalSpace
  refine standardBorelSpace_iff_polish.mpr ⟨t, ?_, @Equiv.polishSpace_induced _ _ up.toTopologicalSpace up.toPolishSpace e.toEquiv⟩
  constructor
  rw [show @borel _ t = _ from borel_comap, ← eq_borel_upgradeStandardBorel]
  exact e.measurableEmbedding.comap_eq.symm

namespace EffrosClosed

variable {X : Type*} [MetricSpace X] [CompleteSpace X] [SeparableSpace X]

/-- The Effros measurable space of all closed subsets of a Polish metric space is standard. -/
theorem standardBorelSpace : StandardBorelSpace (Closeds X) := by
  classical
  cases isEmpty_or_nonempty X with
  | inl hX =>
    have : Subsingleton (Closeds X) := ⟨fun F G => SetLike.coe_injective (Subsingleton.elim _ _)⟩
    have : DiscreteMeasurableSpace (Closeds X) := ⟨fun _ => Subsingleton.measurableSet⟩
    infer_instance
  | inr hX =>
    let : MeasurableSpace X := borel X
    have : BorelSpace X := ⟨rfl⟩
    let x₀ : X := Classical.choice hX
    let F (C : Closeds X) := if (C : Set X).Nonempty then (C : Set X) else {x₀}
    have hne (C : Closeds X) : (F C).Nonempty := by
      by_cases h : (C : Set X).Nonempty
      · simp [F, h]
      · simp [F, h]
    have hc (C : Closeds X) : IsClosed (F C) := by
      by_cases h : (C : Set X).Nonempty
      · simpa [F, h] using C.isClosed
      · simp [F, h]
    have hmeas : ∀ U : Set X, IsOpen U → MeasurableSet {C | (F C ∩ U).Nonempty} := by
      intro U hU
      let N := hit (univ : Set X)
      have hN : MeasurableSet N := measurableSet_hit isOpen_univ
      have he : {C | (F C ∩ U).Nonempty} =
          (N ∩ hit U) ∪ (Nᶜ ∩ {C : Closeds X | x₀ ∈ U}) := by
        ext C
        by_cases h : (C : Set X).Nonempty <;> simp [F, hit, N, h]
      rw [he]
      exact (hN.inter (measurableSet_hit hU)).union (hN.compl.inter (MeasurableSet.const _))
    obtain ⟨s, hs, hclosure⟩ := exists_measurable_dense_selectors F hmeas hne hc
    let code (C : Closeds X) : Bool × (ℕ → X) :=
      (if (C : Set X).Nonempty then true else false, fun n => s n C)
    have hm : Measurable code := by
      refine Measurable.prodMk ?_ (measurable_pi_lambda _ hs)
      exact Measurable.ite (by simpa [hit] using measurableSet_hit (X := X) isOpen_univ)
        measurable_const measurable_const
    refine standardBorel_of_measurable_leftInverse hm measurable_fromCode fun C => ?_
    by_cases h : (C : Set X).Nonempty
    · apply SetLike.coe_injective
      simpa [code, fromCode, F, h] using hclosure C
    · have he : C = ⊥ := SetLike.coe_injective (not_nonempty_iff_eq_empty.mp h)
      simpa [fromCode, code, h] using he.symm

/-- Compact sets form a Borel subset of the Effros space of closed sets. -/
theorem measurableSet_isCompact : MeasurableSet {F : Closeds X | IsCompact (F : Set X)} := by
  classical
  cases isEmpty_or_nonempty X with
  | inl hX =>
    have he : {F : Closeds X | IsCompact (F : Set X)} = univ := by
      ext F
      simp [Subsingleton.elim (F : Set X) (∅ : Set X)]
    rw [he]
    exact MeasurableSet.univ
  | inr hX =>
    let d := denseSeq X
    let r (n : ℕ) : ℝ := 1 / (n + 1)
    have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
    let C (n : ℕ) (s : Finset ℕ) := ⋃ i ∈ s, Metric.closedBall (d i) (r n)
    have hC (n : ℕ) (s : Finset ℕ) : IsClosed (C n s) :=
      s.finite_toSet.isClosed_biUnion fun _ _ => Metric.isClosed_closedBall
    have he : {F : Closeds X | IsCompact (F : Set X)} =
        ⋂ n : ℕ, ⋃ s : Finset ℕ, (hit (C n s)ᶜ)ᶜ := by
      ext F
      simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, mem_compl_iff, hit,
        not_nonempty_inter_compl_iff_subset]
      constructor
      · intro hF n
        obtain ⟨D, hD, hcover⟩ := Metric.totallyBounded_iff.mp hF.totallyBounded
          (r n / 2) (by positivity)
        choose idx hidx using fun x => Metric.denseRange_iff.mp (denseRange_denseSeq X) x
          (r n / 2) (by positivity)
        refine ⟨hD.toFinset.image idx, fun x hx => ?_⟩
        obtain ⟨y, hy⟩ := mem_iUnion.mp (hcover hx)
        obtain ⟨hyD, hxy⟩ := mem_iUnion.mp hy
        refine mem_iUnion.mpr ⟨idx y, mem_iUnion.mpr ⟨Finset.mem_image.mpr
          ⟨y, hD.mem_toFinset.mpr hyD, rfl⟩, ?_⟩⟩
        exact ((dist_triangle x y (d (idx y))).trans_lt (add_lt_add hxy (hidx y))).le.trans_eq
          (by ring)
      · intro hF
        apply TotallyBounded.isCompact_of_isClosed _ F.isClosed
        refine Metric.totallyBounded_iff.mpr fun ε hε => ?_
        obtain ⟨n, hn⟩ := exists_nat_gt (ε⁻¹)
        have hrε : r n < ε := by
          dsimp [r]
          rw [one_div, inv_lt_comm₀ (by positivity) hε]
          linarith
        obtain ⟨s, hs⟩ := hF n
        refine ⟨d '' (s : Set ℕ), (s.finite_toSet.image d), fun x hx => ?_⟩
        obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hx)
        obtain ⟨his, hxi⟩ := mem_iUnion.mp hi
        exact mem_iUnion.mpr ⟨d i, mem_iUnion.mpr ⟨mem_image_of_mem _ his,
          (show dist x (d i) ≤ r n from hxi).trans_lt hrε⟩⟩
    rw [he]
    exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun s =>
      (measurableSet_hit (hC n s).isOpen_compl).compl

end EffrosClosed

/-- On a Polish space the Effros space is standard Borel, and compact sets form
a standard Borel subspace. -/
theorem effros_standardBorel_and_compacts {X : Type*} [TopologicalSpace X] [PolishSpace X] :
    StandardBorelSpace (Closeds X) ∧ MeasurableSet {F : Closeds X | IsCompact (F : Set X)} ∧
      StandardBorelSpace {F : Closeds X // IsCompact (F : Set X)} := by
  let _ := upgradeIsCompletelyMetrizable X
  have hC : StandardBorelSpace (Closeds X) := EffrosClosed.standardBorelSpace
  have hK : MeasurableSet {F : Closeds X | IsCompact (F : Set X)} := EffrosClosed.measurableSet_isCompact
  exact ⟨hC, hK, hK.standardBorel⟩

/-- Nonempty Vietoris compact sets map measurably into the Effros space. -/
theorem measurable_nonemptyCompacts_toCloseds {X : Type*} [TopologicalSpace X] [T2Space X] :
    @Measurable (NonemptyCompacts X) (Closeds X) (borel _) _
      NonemptyCompacts.toCloseds := by
  let : MeasurableSpace (NonemptyCompacts X) := borel _
  have : BorelSpace (NonemptyCompacts X) := ⟨rfl⟩
  apply measurable_generateFrom
  rintro _ ⟨U, hU, rfl⟩
  exact (NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU).measurableSet


/-- Dense Borel selectors suffice for measurability into the Vietoris compact hyperspace. -/
theorem measurable_nonemptyCompacts_of_dense_selectors
    {A X : Type*} [MeasurableSpace A] [MetricSpace X] [SeparableSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] {K : A → NonemptyCompacts X}
    (s : ℕ → A → X) (hs : ∀ n, Measurable (s n))
    (hd : ∀ a, closure (range fun n => s n a) = (K a : Set X)) :
    @Measurable A (NonemptyCompacts X) _ (borel _) K := by
  let : MeasurableSpace (NonemptyCompacts X) := borel _
  have hHit (U : Set X) (hU : IsOpen U) :
      MeasurableSet {a | ((K a : Set X) ∩ U).Nonempty} := by
    have he : {a | ((K a : Set X) ∩ U).Nonempty} = ⋃ n, s n ⁻¹' U := by
      ext a
      change ((K a : Set X) ∩ U).Nonempty ↔ _
      rw [← hd a, closure_inter_open_nonempty_iff hU]
      simp only [mem_iUnion, mem_preimage, Set.inter_nonempty, mem_range]
      exact ⟨fun ⟨_, ⟨n, rfl⟩, hn⟩ => ⟨n, hn⟩, fun ⟨n, hn⟩ => ⟨_, mem_range_self n, hn⟩⟩
    rw [he]
    exact MeasurableSet.iUnion fun n => hs n hU.measurableSet
  have hSubset (U : Set X) (hU : IsOpen U) : MeasurableSet {a | (K a : Set X) ⊆ U} := by
    rcases (Uᶜ).eq_empty_or_nonempty with h | h
    · have hU' : U = univ := by
        apply compl_injective
        simpa using h
      simp [hU']
    · have hm := measurableSet_hit_compact_inter_closed
        (fun a => (K a : Set X)) (fun _ => Uᶜ) (fun a => (K a).isCompact)
        (fun _ => hU.isClosed_compl) (fun _ => h) ⟨s, hs, hd⟩
        (fun _ _ => MeasurableSet.const _) isOpen_univ
      simpa only [compl_ofPred, inter_univ, not_nonempty_inter_compl_iff_subset] using hm.compl
  change @Measurable _ _ _ (borel _) K
  rw [NonemptyCompacts.isTopologicalBasis.borel_eq_generateFrom]
  apply measurable_generateFrom
  rintro _ ⟨u, ⟨hu, _, hU⟩, rfl⟩
  have he : K ⁻¹' {L : NonemptyCompacts X | (L : Set X) ⊆ ⋃₀ u ∧
        ∀ U ∈ u, ((L : Set X) ∩ U).Nonempty} =
      {a | (K a : Set X) ⊆ ⋃₀ u} ∩ ⋂ U ∈ u, {a | ((K a : Set X) ∩ U).Nonempty} := by
    ext a
    simp
  rw [he]
  exact (hSubset _ (isOpen_sUnion hU)).inter (MeasurableSet.biInter hu.countable fun U h =>
    hHit U (hU U h))

end PaperFormalization
