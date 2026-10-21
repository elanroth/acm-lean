-- `lean_lib Test` roots at this file, so a regression module that is not imported
-- here is never compiled by `lake build` and cannot fail.  Every module under
-- `Test/` must appear below.
import Test.UlmRegression
import Test.EvenWindowRegression
import Test.JumpSpaceRegression
import Test.InducedMapRegression
import Test.JumpWitness
import Test.D5Example
import Test.FiniteRadoRegression
import Test.KernelRoomRegression
import Test.SocleLiftRegression
import Test.FiniteSocleRegression
import Test.FiniteEmbeddingRegression
import Test.LocalFiniteEmbeddingRegression
import Test.EvenExtensionRegression
import Test.ScottComplexityRegression
import Test.CharacterizationRegression
import Test.NonVacuityRegression
import Test.UlmDifferentialRegression
import Test.AxiomGate
