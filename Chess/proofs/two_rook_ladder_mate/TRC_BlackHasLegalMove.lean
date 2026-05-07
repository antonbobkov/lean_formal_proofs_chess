import ChessRules
import TRC_FunctionWithInvariant
import LadderStepIsLegal
import TRC_FinalState

-- ============================================================
-- BLACK HAS A LEGAL REPLY (UNLESS FINAL)
-- ============================================================
-- For any non-final ladder state, the Black king has at least one legal
-- destination after applyLadderStep. Proof outline by phase:
--   • moveRb / moveK post-step: no rook attacks the Black king's rank,
--     so the king can step sideways or upward.
--   • moveRa post-step (rank.val + 3 < n, i.e. NOT final): the Black
--     king is forced to rank n-1 only when rank.val + 3 = n; otherwise
--     it has room to retreat upward to rank+3.

lemma Black_HasLegalReply_NonFinal {n : Nat} (s : LadderState n)
    (h_not_final : ¬ IsFinalLadderState s) :
    ∃ src dst : Pos n, IsLegalMove (applyLadderStep s.shape) src dst := by
  sorry

-- Helper: classical-choice extraction of a witness as a (src, dst) pair,
-- which is the type expected by `step` / `hreply` in the termination proof.
noncomputable def blackLegalReply {n : Nat} (s : LadderState n)
    (h_not_final : ¬ IsFinalLadderState s) : Pos n × Pos n :=
  let ⟨src, hsrc⟩ := Classical.indefiniteDescription _
                       (Black_HasLegalReply_NonFinal s h_not_final)
  let ⟨dst, _⟩ := Classical.indefiniteDescription _ hsrc
  (src, dst)

lemma blackLegalReply_isLegal {n : Nat} (s : LadderState n)
    (h_not_final : ¬ IsFinalLadderState s) :
    IsLegalMove (applyLadderStep s.shape)
      (blackLegalReply s h_not_final).1 (blackLegalReply s h_not_final).2 := by
  sorry
