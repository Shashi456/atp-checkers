import Lake
open Lake DSL

package «atp-checkers» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.24.0"

lean_lib «AtpLinter» where
  srcDir := "src"
  roots := #[`AtpLinter]

lean_lib «AtpLinterTest» where
  srcDir := "test"
  roots := #[`AllTests]

lean_lib «AtpLinterDemo» where
  srcDir := "test"
  roots := #[`DemoTests]

@[default_target]
lean_exe «atp-checkers» where
  root := `Main
