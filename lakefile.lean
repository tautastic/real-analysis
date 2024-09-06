import Lake
open Lake DSL

package "RealAnalysis" where
  -- add package configuration options here

require "leanprover-community" / "mathlib"

@[default_target]
lean_lib «RealAnalysis» where
