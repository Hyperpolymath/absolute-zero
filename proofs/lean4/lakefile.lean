import Lake
open Lake DSL

package cno where
  -- Add package configuration here

lean_lib CNO where
  -- Add library configuration here

@[default_target]
lean_exe absolute_zero where
  root := `CNO
  -- Add more executable configuration here
