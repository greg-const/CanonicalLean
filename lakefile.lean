import Lake
open Lake DSL

package Canonical where
  precompileModules := true

target canonical : Dynlib := do pure $ Job.pure {
  path := __dir__ / ".lake" / "build" / "lib" / nameToSharedLib "canonical_lean"
  name := "canonical_lean"
}

@[default_target]
lean_lib Canonical {moreLinkLibs := #[canonical]}
