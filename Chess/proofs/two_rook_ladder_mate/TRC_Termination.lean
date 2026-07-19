import ChessRules
import TRC_FunctionWithInvariant
import TRC_Invariant_Preservation
import TRC_FinalState
import TRC_BlackHasLegalMove
import LadderStepIsLegal

-- ============================================================
-- TERMINATION / CHECKMATE THEOREM
-- ============================================================
-- The ladder forces checkmate for Black in finitely many cycles
-- (one White ply + one legal Black ply each), regardless of how Black
-- plays.
--
-- `reply` is an arbitrary Black strategy: given the board after the
-- White ply it picks (src, dst). `hreply` witnesses that every chosen
-- move is legal. We iterate `ladderCycleStep` (one full cycle) until
-- a final state is reached, at which point `applyLadderStep` delivers
-- checkmate.
--
-- `hreply` is required only at *non-final* states. This matters: at a
-- final state Black is checkmated, so no legal Black move exists there
-- and an unrestricted `hreply` would be unsatisfiable — making the
-- termination theorem vacuously true. `Black_HasLegalReply_NonFinal`
-- (with `blackLegalReply` / `blackLegalReply_isLegal`) supplies a
-- witness that the restricted hypothesis is inhabited.

-- One full ladder cycle as a step on `LadderState`. Final states are
-- fixed points: once Black is mated there is nothing left to play, and
-- stopping there keeps the function total without needing a Black reply.
-- The boundary precondition for `LadderShape.preservation`
-- (φ = .moveK → rank+3 < n) is automatic via `LadderShape.moveK_hRoom`.
def ladderCycleStep {n : Nat}
    (reply : (b : Board n) → Pos n × Pos n)
    (hreply : ∀ s : LadderState n, ¬ IsFinalLadderState s →
        IsLegalMove (applyLadderStep s.shape)
          (reply (applyLadderStep s.shape)).1
          (reply (applyLadderStep s.shape)).2)
    (s : LadderState n) : LadderState n :=
  if hfin : IsFinalLadderState s then s
  else
    { board := applyMove (applyLadderStep s.shape)
                 (reply (applyLadderStep s.shape)).1
                 (reply (applyLadderStep s.shape)).2
      rank  := nextRank s.rank s.phase s.shape.hRfits
      phase := nextPhase s.phase
      shape := LadderShape.preservation s.shape
                (fun h => (h ▸ s.shape : LadderShape s.board s.rank .moveK).moveK_hRoom)
                (hreply s hfin) }

-- ------------------------------------------------------------
-- TERMINATION MEASURE
-- ------------------------------------------------------------
-- The lexicographic pair (rank-room-left, phase-distance-to-moveK)
-- flattened into a single Nat: three phases per rank, so a phase
-- advance drops the measure by one and a rank advance (which resets
-- the phase to the top of the cycle) still drops it by one overall.
def phaseIdx : LadderPhase → Nat
  | .moveRb => 2
  | .moveRa => 1
  | .moveK  => 0

def ladderMeasure {n : Nat} (s : LadderState n) : Nat :=
  3 * (n - 3 - s.rank.val) + phaseIdx s.phase

-- The arithmetic core, stated on a bare rank/phase pair so that casing
-- on the phase does not have to drag a `LadderShape` along. The `.moveK`
-- case is the interesting one: the rank advances, so the first component
-- drops by 3 while the phase index climbs back from 0 to 2 — a net
-- decrease of 1. It needs `rank + 3 < n` (there really is another rank
-- to climb to).
lemma ladderMeasure_arith {n : Nat} (r : Fin n) (φ : LadderPhase)
    (hfits : r.val + 2 < n) (hroom : φ = .moveK → r.val + 3 < n) :
    3 * (n - 3 - (nextRank r φ hfits).val) + phaseIdx (nextPhase φ)
      < 3 * (n - 3 - r.val) + phaseIdx φ := by
  cases φ
  · simp only [nextRank, nextPhase, phaseIdx]; omega
  · simp only [nextRank, nextPhase, phaseIdx]; omega
  · have hroom' := hroom rfl
    simp only [nextRank, nextPhase, phaseIdx]
    omega

-- Away from a final state the cycle strictly decreases the measure.
-- `LadderShape.moveK_hRoom` supplies the `.moveK` room bound.
lemma ladderMeasure_decreases {n : Nat}
    (reply : (b : Board n) → Pos n × Pos n)
    (hreply : ∀ s : LadderState n, ¬ IsFinalLadderState s →
        IsLegalMove (applyLadderStep s.shape)
          (reply (applyLadderStep s.shape)).1
          (reply (applyLadderStep s.shape)).2)
    (s : LadderState n) (hfin : ¬ IsFinalLadderState s) :
    ladderMeasure (ladderCycleStep reply hreply s) < ladderMeasure s := by
  have hrank : (ladderCycleStep reply hreply s).rank
      = nextRank s.rank s.phase s.shape.hRfits := by
    simp only [ladderCycleStep, dif_neg hfin]
  have hphase : (ladderCycleStep reply hreply s).phase = nextPhase s.phase := by
    simp only [ladderCycleStep, dif_neg hfin]
  simp only [ladderMeasure, hrank, hphase]
  exact ladderMeasure_arith s.rank s.phase s.shape.hRfits
    (fun h => (h ▸ s.shape : LadderShape s.board s.rank .moveK).moveK_hRoom)

-- Fuel-style version of the statement below: `m` bounds the measure, and
-- ordinary induction on `m` replaces well-founded recursion. A state that
-- is not already final steps to one of strictly smaller measure, so the
-- bound drops and the induction hypothesis applies.
private lemma exists_iter_final_aux {n : Nat}
    (reply  : (b : Board n) → Pos n × Pos n)
    (hreply : ∀ s : LadderState n, ¬ IsFinalLadderState s →
        IsLegalMove (applyLadderStep s.shape)
          (reply (applyLadderStep s.shape)).1
          (reply (applyLadderStep s.shape)).2) :
    ∀ (m : Nat) (s : LadderState n), ladderMeasure s ≤ m →
      ∃ k : Nat, IsFinalLadderState ((ladderCycleStep reply hreply)^[k] s) := by
  intro m
  induction m with
  | zero =>
    intro s hs
    by_cases hfin : IsFinalLadderState s
    · exact ⟨0, hfin⟩
    · -- measure 0 with a strictly smaller successor is impossible
      have := ladderMeasure_decreases reply hreply s hfin
      omega
  | succ m ih =>
    intro s hs
    by_cases hfin : IsFinalLadderState s
    · exact ⟨0, hfin⟩
    · have hlt := ladderMeasure_decreases reply hreply s hfin
      obtain ⟨k, hk⟩ := ih (ladderCycleStep reply hreply s) (by omega)
      exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

-- The iteration of `ladderCycleStep` reaches a final state after some
-- number of cycles, by induction on `ladderMeasure`, which
-- `ladderMeasure_decreases` drops on every non-final cycle.
lemma exists_iter_final {n : Nat} (s₀ : LadderState n)
    (reply  : (b : Board n) → Pos n × Pos n)
    (hreply : ∀ s : LadderState n, ¬ IsFinalLadderState s →
        IsLegalMove (applyLadderStep s.shape)
          (reply (applyLadderStep s.shape)).1
          (reply (applyLadderStep s.shape)).2) :
    ∃ k : Nat,
      IsFinalLadderState ((ladderCycleStep reply hreply)^[k] s₀) :=
  exists_iter_final_aux reply hreply (ladderMeasure s₀) s₀ le_rfl

-- The ladder forces checkmate for Black in finitely many cycles.
theorem ladderMate_termination {n : Nat}
    (s₀     : LadderState n)
    (reply  : (b : Board n) → Pos n × Pos n)
    (hreply : ∀ s : LadderState n, ¬ IsFinalLadderState s →
        IsLegalMove (applyLadderStep s.shape)
          (reply (applyLadderStep s.shape)).1
          (reply (applyLadderStep s.shape)).2) :
    ∃ k : Nat,
      IsCheckmate
        (applyLadderStep ((ladderCycleStep reply hreply)^[k] s₀).shape)
        .Black := by
  obtain ⟨k, hfinal⟩ := exists_iter_final s₀ reply hreply
  exact ⟨k, IsCheckmate_AtFinal _ hfinal⟩
