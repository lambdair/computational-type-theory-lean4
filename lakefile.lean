import Lake
open Lake DSL

package "computational-type-theory-lean4" where
  -- add package configuration options here

lean_lib «ComputationalTypeTheoryLean4» where
  -- add library configuration options here

@[default_target]
lean_exe "computational-type-theory-lean4" where
  root := `Main
