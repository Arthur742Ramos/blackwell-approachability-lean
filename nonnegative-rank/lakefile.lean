import Lake
open Lake DSL

package «finite_nonnegative_rank» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "db584cd6d46c92f209a44c0f1c829460d327499d"

@[default_target]
lean_lib NonnegativeRankChallenge

@[default_target]
lean_lib NonnegativeRankSolution

@[default_target]
lean_lib NonnegativeRankExamples
