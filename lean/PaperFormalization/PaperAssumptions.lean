import PaperFormalization.BanachProperties

namespace PaperFormalization

open TopologicalSpace

/-! # External theorem
Enflo, Acta Mathematica 130 (1973), Theorem 1, constructs a separable reflexive
real Banach space without the approximation property. We use only the weaker
existence conclusion below. This is the sole external mathematical axiom of
the project. Its use is reported by the terminal audit. -/

/-- Enflo's existence result: a separable real Banach space without AP. -/
axiom enfloNoAP :
  ∃ E : RealBanachSpace, SeparableSpace E ∧ ¬ HasApproximationProperty E

end PaperFormalization
