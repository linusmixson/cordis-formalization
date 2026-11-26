-- Paper-indexed results and literal counterexamples.
import Cordis.Results.Context
import Cordis.Results.Rules
import Cordis.Results.Counterexamples
import Cordis.Results.Support
import Cordis.Results.GlobalSupport
import Cordis.TypedRegistryFrame
import Cordis.Results.TypedGlobalSupport
import Cordis.Results.TypedRules
import Cordis.Results.TypedSupportCounterexample
import Cordis.Results.TypedTransposition
import Cordis.Results.CanonicalOrderCounterexample
import Cordis.Results.GlobalProvisionContradiction
-- Scoped operations, name transport and support.
import Cordis.Repairs.ProvisionExample
import Cordis.Repairs.ProvisionConfinement
import Cordis.Repairs.OperationExample
import Cordis.Repairs.OperationConfinement
import Cordis.Repairs.AllocationDomains
import Cordis.Repairs.ScopedProgramExample
import Cordis.Repairs.Lemma61
import Cordis.Repairs.CausalOrderExample
import Cordis.Repairs.CommandBarrier
import Cordis.Repairs.IncarnationExample
import Cordis.Repairs.EpisodeSelection
import Cordis.Repairs.SupportLinearizationExample
import Cordis.Repairs.EpisodeDependencies
import Cordis.Repairs.EpisodeBoundary
import Cordis.Repairs.EpisodeRollback
import Cordis.Repairs.EpisodeOperationReplay
import Cordis.Repairs.EpisodeInterior
import Cordis.Repairs.EpisodeSuffix
import Cordis.Repairs.EpisodeClosureExample
-- Guarded histories, replay and schedule alignment.
import Cordis.Repairs.GuardedEpisodeExample
import Cordis.Repairs.GuardedBirthExample
import Cordis.Repairs.GuardedPartialComparison
import Cordis.Repairs.FrozenGuardedApplications
import Cordis.Repairs.ScopedEquation54
import Cordis.Repairs.ReplayBindingExample
import Cordis.Repairs.GuardedNormalization
import Cordis.Repairs.GuardedOpenExchange
import Cordis.Repairs.GuardedActivationExchange
import Cordis.Repairs.GuardedActivationOrder
import Cordis.Repairs.GuardedActivationAlignment
import Cordis.Repairs.GuardedIncarnationRedraw
import Cordis.Repairs.GuardedCompleteAlignment
import Cordis.Repairs.GuardedNameExtension
import Cordis.Repairs.EpisodeReleaseBarrier
-- Scoped independence and selected-yield preservation.
import Cordis.Repairs.PairwiseAllocationExample
import Cordis.Repairs.PairwiseOperations
import Cordis.Repairs.PairwiseForward
import Cordis.Repairs.PairwisePrograms
import Cordis.Repairs.PairwiseReplay
import Cordis.Repairs.PairwiseSlots
import Cordis.Repairs.PairwiseMixed
import Cordis.Repairs.PairwiseNativeWords
import Cordis.Repairs.ScopedIteratorGenerators
import Cordis.Repairs.ScopedAdmissionExchange
import Cordis.Repairs.Lemma66
-- Canonical schedules, confluence and boundary examples.
import Cordis.Repairs.EpisodeInterleaving
import Cordis.Repairs.GuardedCausalOrder
import Cordis.Repairs.GuardedCanonicalOrder
import Cordis.Repairs.GuardedConfluence
import Cordis.Repairs.GuardedCanonicalSchedule
import Cordis.Repairs.ChildCommandConfluence
import Cordis.Repairs.EpisodeAddressConfluence
import Cordis.Repairs.GuardedReservationExample
import Cordis.Repairs.StagePriorityExample
import Cordis.Repairs.PinnedRedrawExample
import Cordis.Repairs.EntangledCleanupBoundary
import Cordis.Repairs.EquivariantReuseCounterexample
import Cordis.Repairs.CodeMap
import Cordis.Repairs.NominalConfluence
import Cordis.Repairs.NominalOpenConfluence
import Cordis.Repairs.FreshDrawsNecessary
-- Audit all imported project declarations and their dependencies.
import Cordis.AxiomAudit

/-! Lean formalization of the numbered lemmas in arXiv:2608.25512v1. -/

run_cmd Cordis.AxiomAudit.check `Cordis
