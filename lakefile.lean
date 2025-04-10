import Lake
open Lake DSL

package Canonical where
  precompileModules := true
  moreLinkArgs := #[ "-L", (__dir__ / ".lake" / "build" / "lib").toString, "-l", "canonical" ]

@[default_target]
lean_lib Canonical
