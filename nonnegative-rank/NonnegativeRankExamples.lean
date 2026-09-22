import NonnegativeRankSolution

namespace Blackwell.NonnegativeRank.Palomar

example : HasProductMixture (uniformDiagonal 2) 2 := by
  exact uniformDiagonal_has_productMixture (by norm_num)

example {k : ℕ} (h : HasProductMixture (uniformDiagonal 3) k) : 3 ≤ k := by
  exact uniformDiagonal_mixture_minimal (by norm_num) h

end Blackwell.NonnegativeRank.Palomar
