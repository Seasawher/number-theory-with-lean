import Lake
open Lake DSL

package «NTL» where
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "e9bcfc6e583d0784ece32475ca6f450126ef286f"

@[default_target]
lean_lib «NTL» where
  -- add any library configuration options here
