import Lake
open Lake DSL

package «atp-checkers» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.24.0"

lean_lib «AtpLinter» where
  srcDir := "src"
  roots := #[`AtpLinter]

lean_lib «AtpLinterTest» where
  srcDir := "test"
  globs := #[.one `AllTests, .one `ArithmeticSemanticsTests, .one `GuardProvingTests, .one `PrefixScopeTests, .one `StructuralCheckerTests, .one `AdvancedCheckerTests, .one `IntegrationTests, .one `CoverageTests]

lean_lib «AtpLinterDemo» where
  srcDir := "test"
  globs := #[.one `DemoTests, .one `Examples, .one `SimpleExamples, .one `RealProblem]

@[default_target]
lean_exe «atp-checkers» where
  root := `Main
