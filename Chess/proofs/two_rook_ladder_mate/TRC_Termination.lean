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

-- The iteration of `ladderCycleStep` reaches a final state after some
-- number of cycles. Proof by induction on the lexicographic measure
-- (n - 3 - s.rank.val, phase-distance-to-moveRa).
lemma exists_iter_final {n : Nat} (s₀ : LadderState n)
    (reply  : (b : Board n) → Pos n × Pos n)
    (hreply : ∀ s : LadderState n, ¬ IsFinalLadderState s →
        IsLegalMove (applyLadderStep s.shape)
          (reply (applyLadderStep s.shape)).1
          (reply (applyLadderStep s.shape)).2) :
    ∃ k : Nat,
      IsFinalLadderState ((ladderCycleStep reply hreply)^[k] s₀) := by
  sorry

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
