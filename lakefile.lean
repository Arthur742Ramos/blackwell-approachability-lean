import Lake
open Lake DSL

package «blackwell_approachability» where
  version := v!"0.6.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "db584cd6d46c92f209a44c0f1c829460d327499d"

@[default_target]
lean_lib BlackwellApproachability

@[default_target]
lean_lib BlackwellGame

@[default_target]
lean_lib BlackwellReduction

@[default_target]
lean_lib BlackwellMinimax

@[default_target]
lean_lib BlackwellIrreducibility

@[default_target]
lean_lib BlackwellIrreducibilityExamples

@[default_target]
lean_lib BlackwellChallenge

@[default_target]
lean_lib BlackwellSolution

@[default_target]
lean_lib BlackwellExamples

@[default_target]
lean_lib BlackwellGameExamples

@[default_target]
lean_lib BlackwellSubstantiveExamples
