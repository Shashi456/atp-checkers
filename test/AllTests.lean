/-
  AllTests — imports gating test files so `lake build AtpLinterTest` compiles them all.
  Demo/example files are in DemoTests.lean (separate root).
-/

import TestAssertions
import ArithmeticSemanticsTests
import GuardProvingTests
import PrefixScopeTests
import StructuralCheckerTests
import AdvancedCheckerTests
import IntegrationTests
import CoverageTests
