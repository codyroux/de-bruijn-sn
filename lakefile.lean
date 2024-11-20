import Lake
open Lake DSL

package «de-bruijn-sn» where
  -- add package configuration options here

lean_lib «DeBruijnSn» where
  -- add library configuration options here

@[default_target]
lean_exe «de-bruijn-sn» where
  root := `Main
