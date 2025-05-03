import Lake
open Lake DSL

package Canonical

target canonical pkg : Dynlib := do pure $ Job.pure {
  path := pkg.sharedLibDir / nameToSharedLib "canonical_lean"
  name := "canonical_lean"
}

@[default_target]
lean_lib Canonical where
  precompileModules := true
  moreLinkLibs := #[canonical]
