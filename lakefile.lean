import Lake
open Lake DSL

package «theorem-proving-in-lean» where
  -- add package configuration options here

lean_lib «TheoremProvingInLean» where
  -- add library configuration options here

@[default_target]
lean_exe «theorem-proving-in-lean» where
  root := `Main
