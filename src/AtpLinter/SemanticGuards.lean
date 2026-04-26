/-
  Semantic Guard Prover facade.

  Existing checkers import this module. The implementation is split across:
  - `GuardFacts`: local fact discovery and bounded fact expansion
  - `GuardProver`: proof orchestration and checker-facing entry points
  - `GuardPolicy`: binder-safe local-context policy re-exported through Basic
-/

import AtpLinter.GuardProver

namespace AtpLinter
namespace SemanticGuards

end SemanticGuards
end AtpLinter
