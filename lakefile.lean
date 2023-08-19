import Lake
open Lake DSL

package «arithmetics» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"axgroth"

@[default_target]
lean_lib «Arithmetics» {
  -- add any library configuration options here
}
