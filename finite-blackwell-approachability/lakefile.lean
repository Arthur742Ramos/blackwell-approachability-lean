import Lake
open Lake DSL

package «finite_blackwell_approachability» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "db584cd6d46c92f209a44c0f1c829460d327499d"

@[default_target]
lean_lib FiniteBlackwell

@[default_target]
lean_lib ApproachabilityCore

@[default_target]
lean_lib FiniteBlackwellRate

@[default_target]
lean_lib FiniteBlackwellChallenge

@[default_target]
lean_lib FiniteBlackwellSolution

@[default_target]
lean_lib FiniteBlackwellExamples
