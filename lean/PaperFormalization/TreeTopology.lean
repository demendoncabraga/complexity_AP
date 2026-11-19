import PaperFormalization.Basic

namespace PaperFormalization.NatTree

/-- The characteristic function in the product of discrete two-point spaces. -/
noncomputable def code (T : NatTree) (s : List ℕ) : Bool :=
  @decide (s ∈ T.val) (Classical.propDecidable _)

noncomputable instance instTopologicalSpace : TopologicalSpace NatTree :=
  TopologicalSpace.induced code inferInstance

noncomputable instance instMeasurableSpace : MeasurableSpace NatTree := borel NatTree

instance instBorelSpace : BorelSpace NatTree := ⟨rfl⟩

theorem isClopen_nodes (s : List ℕ) : IsClopen {T : NatTree | s ∈ T.val} := by
  have hc : Continuous (fun T : NatTree => code T s) :=
    (continuous_apply s).comp (continuous_induced_dom (f := code))
  convert (isClopen_discrete ({true} : Set Bool)).preimage hc using 1
  exact Set.ext fun T => by simp [code]

theorem isClosed_range_code : IsClosed (Set.range code) := by
  classical
  have hrange : Set.range code =
      ⋂ (s : List ℕ) (t : List ℕ) (_ : s <+: t),
        ((fun f : List ℕ → Bool => f t) ⁻¹' {false} ∪
          (fun f : List ℕ → Bool => f s) ⁻¹' {true}) := by
    ext f
    simp only [Set.mem_range, Set.mem_iInter, Set.mem_union, Set.mem_preimage,
      Set.mem_singleton_iff]
    exact ⟨fun ⟨T, he⟩ s t hst => by
      subst f
      by_cases ht : t ∈ T.val
      · exact Or.inr (by simp [code, T.property s t hst ht])
      · exact Or.inl (by simp [code, ht]),
      fun hf => ⟨⟨{s | f s = true}, fun s t hst ht =>
        (hf s t hst).resolve_left (by simp [show f t = true from ht])⟩,
        funext fun s => by cases hs : f s <;> simp [code, hs]⟩⟩
  exact hrange ▸ isClosed_iInter fun s => isClosed_iInter fun t =>
    isClosed_iInter fun _ => (isClosed_singleton.preimage (continuous_apply t)).union
      (isClosed_singleton.preimage (continuous_apply s))

theorem isClosedEmbedding_code : Topology.IsClosedEmbedding code :=
  ⟨⟨⟨rfl⟩, fun T U h => Subtype.ext (Set.ext fun s => by
    simpa [code] using congrArg (fun f : List ℕ → Bool => f s = true) h)⟩,
    isClosed_range_code⟩

instance instPolishSpace : PolishSpace NatTree := by
  let _ := TopologicalSpace.upgradeIsCompletelyMetrizable Bool
  let _ : MetricSpace (List ℕ → Bool) := PiCountable.metricSpace
  exact isClosedEmbedding_code.polishSpace

theorem isClosed_branchRelation :
    IsClosed {p : NatTree × (ℕ → ℕ) | p.2 ∈ p.1.branches} := by
  have he : {p : NatTree × (ℕ → ℕ) | p.2 ∈ p.1.branches} =
      ⋂ n : ℕ, {p : NatTree × (ℕ → ℕ) |
        List.ofFn (fun i : Fin n => p.2 i) ∈ p.1.val} := by
    ext p
    simp [branches]
  rw [he]
  refine isClosed_iInter fun n => ?_
  let _ : TopologicalSpace (List ℕ) := ⊥
  let _ : DiscreteTopology (List ℕ) := ⟨rfl⟩
  have hprefix : Continuous (fun b : ℕ → ℕ => List.ofFn fun i : Fin n => b i) :=
    (continuous_of_discreteTopology : Continuous (List.ofFn : (Fin n → ℕ) → List ℕ)).comp
      (continuous_pi fun i : Fin n => continuous_apply i.val)
  have heval : Continuous (fun p : NatTree × List ℕ => code p.1 p.2) :=
    continuous_prod_of_discrete_right.mpr fun s =>
      (continuous_apply s).comp (continuous_induced_dom (f := code))
  have hset : {p : NatTree × (ℕ → ℕ) | List.ofFn (fun i : Fin n => p.2 i) ∈ p.1.val} =
      (fun p : NatTree × (ℕ → ℕ) => code p.1 (List.ofFn fun i : Fin n => p.2 i)) ⁻¹'
        ({true} : Set Bool) := Set.ext fun p => by simp [code]
  exact hset.symm ▸ isClosed_singleton.preimage
    (heval.comp (continuous_fst.prodMk (hprefix.comp continuous_snd)))

theorem analyticSet_illFounded : MeasureTheory.AnalyticSet {T : NatTree | T.IsIllFounded} := by
  have himage : Prod.fst '' {p : NatTree × (ℕ → ℕ) | p.2 ∈ p.1.branches} =
      {T : NatTree | T.IsIllFounded} := by
    ext T
    simp [Set.mem_image, IsIllFounded, Set.Nonempty]
  rw [← himage]
  let _ := TopologicalSpace.upgradeIsCompletelyMetrizable NatTree
  let _ : MetricSpace (ℕ → ℕ) := PiNat.metricSpaceNatNat
  exact isClosed_branchRelation.analyticSet.image_of_continuous continuous_fst

end PaperFormalization.NatTree
