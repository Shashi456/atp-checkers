/-
  Public semantic-guard facade.

  This module is intentionally small. Existing checkers import
  `AtpLinter.SemanticGuards`, while the implementation is split by concern:

  - `GuardPolicy`: binder-safe local-context construction
  - `GuardFacts`: local fact discovery and bounded fact expansion
  - `GuardProver`: proof orchestration and checker-facing guard queries

  Keep checker-facing imports pointed here unless code needs an internal helper.
  That preserves a stable public boundary while allowing the guard machinery to
  stay split by responsibility.
-/

import AtpLinter.GuardProver

namespace AtpLinter
namespace SemanticGuards

end SemanticGuards
end AtpLinter
