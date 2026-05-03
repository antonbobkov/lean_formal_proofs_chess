import ChessRules
import TRC_FunctionWithInvariant
import TRC_Invariant_PieceLocations

-- ------------------------------------------------------------
-- HELPERS FOR Q PRESERVATION (white pieces confined to K, Rb, Ra)
-- ------------------------------------------------------------
-- The Q conjunct of `LadderShape` says the only white-occupied
-- squares are the three named ladder squares. After one White ply
-- + one legal Black reply (with bdst empty), Q on the input board
-- transports to Q on the output board via the counting machinery
-- in `HelperLemmas`:
--
--   (1) `colorSquares_card_le_three_of_Q` turns input Q into
--       a `card ≤ 3` bound on white squares.
--   (2) `colorSquares_card_eq_ourMove` carries that bound through
--       the white ply (white's own legal move can't add a fresh
--       white square — captures only swap an opponent square for
--       a white one), and `colorSquares_card_eq_nonCapture` carries
--       it through the black ply (target empty by hypothesis).
--   (3) `Q_of_subset_card_le` collapses the bound back to Q on the
--       output board, given the three named squares each carry a
--       white piece (from `applyLadderStep_PiecesAt_*` + `whitePiecePreserved`)
--       and are pairwise distinct (the three lemmas just below).

-- The three named ladder squares (kingPos, rookBPos, rookAPos) are
-- pairwise distinct for every phase. Each pair separates either by
-- file or by rank; the value table in `TRC_FunctionWithInvariant.lean`
-- shows the gap explicitly.
lemma ladderPos_pairwise_distinct {n : Nat} (rank : Fin n) (φ : LadderPhase)
    (h : rank.val + 2 < n) :
    kingPos rank h ≠ rookBPos rank φ h ∧
    kingPos rank h ≠ rookAPos rank φ h ∧
    rookBPos rank φ h ≠ rookAPos rank φ h := by
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    have := congrArg (fun p : Pos n => p.file.val) heq
    cases φ <;> simp [kingPos, rookBPos] at this
  · intro heq
    have := congrArg (fun p : Pos n => p.rank.val) heq
    cases φ <;> simp [kingPos, rookAPos] at this
  · intro heq
    have := congrArg (fun p : Pos n => p.file.val) heq
    cases φ <;> simp [rookBPos, rookAPos] at this

-- After White's ladder ply the count of white-occupied squares is
-- unchanged: the ply targets an empty square (`LadderMove_IntoEmptySquare`),
-- so it doesn't drop a piece on top of an existing white-occupied square.
-- Combined with the input Q, this gives the `≤ 3` bound on the step
-- board's white squares — the seed needed to recover Q on the step
-- board (used both by the full-cycle bound below and by
-- `LadderMove_OnlyFileOneRaRank_InRegion`).
lemma whiteCount_le_three_after_step {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    (lsh : LadderShape board rank φ) :
    (colorSquares (applyLadderStep lsh) .White).card ≤ 3 := by
  obtain ⟨_, _, _, _, hQ, _, _, _⟩ := lsh.unfold
  have h_init : (colorSquares board .White).card ≤ 3 :=
    colorSquares_card_le_three_of_Q board .White hQ
  have h_white_ply : (colorSquares (applyLadderStep lsh) .White).card =
      (colorSquares board .White).card :=
    colorSquares_card_eq_nonCapture board .White
      (ladderStep lsh).1 (ladderStep lsh).2
      (LadderMove_IntoEmptySquare lsh)
  omega

-- Extends `whiteCount_le_three_after_step` across the Black ply: the
-- black ply also targets an empty square (`bdst_empty`), so the count
-- is preserved a second time.
lemma whiteCount_le_three_after_cycle {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    (lsh : LadderShape board rank φ) {bsrc bdst : Pos n}
    (bdst_empty : (applyLadderStep lsh) bdst = none) :
    (colorSquares (applyMove (applyLadderStep lsh) bsrc bdst) .White).card ≤ 3 := by
  have h_step := whiteCount_le_three_after_step lsh
  have h_black_ply :
      (colorSquares (applyMove (applyLadderStep lsh) bsrc bdst) .White).card =
      (colorSquares (applyLadderStep lsh) .White).card :=
    colorSquares_card_eq_nonCapture (applyLadderStep lsh) .White
      bsrc bdst bdst_empty
  omega


-- ------------------------------------------------------------
-- Q ON THE STEP BOARD
-- ------------------------------------------------------------
-- Companions to `applyLadderStep_PiecesAt_*`: not only do the three named
-- squares carry white pieces after White's ply, those are the *only*
-- squares carrying white pieces. Recovered from the input Q via the
-- counting machinery — `whiteCount_le_three_after_step` for the count
-- bound and the `applyLadderStep_PiecesAt_*` triple plus
-- `ladderPos_pairwise_distinct` for the saturating subset, fed into
-- `Q_of_subset_card_le`.
--
-- Like `applyLadderStep_PiecesAt_*`, the three squares are phase-dependent
-- (they are the next state's named positions), so this is split into
-- one lemma per input phase.

lemma applyLadderStep_QPart_moveRb {n : Nat} {board : Board n} {rank : Fin n}
    (lsh : LadderShape board rank .moveRb) :
    let h := lsh.hRfits
    let b' := applyLadderStep lsh
    ∀ p, (∃ k, b' p = some ⟨.White, k⟩) →
         p = kingPos rank h ∨
         p = rookBPos rank .moveRa h ∨
         p = rookAPos rank .moveRa h := by
  obtain ⟨hK, hRb, hRa⟩ := applyLadderStep_PiecesAt_moveRb lsh
  exact Q_of_subset_card_le _ .White
    ⟨.King, hK⟩ ⟨.Rook, hRb⟩ ⟨.Rook, hRa⟩
    (ladderPos_pairwise_distinct rank .moveRa lsh.hRfits)
    (whiteCount_le_three_after_step lsh)

lemma applyLadderStep_QPart_moveRa {n : Nat} {board : Board n} {rank : Fin n}
    (lsh : LadderShape board rank .moveRa) :
    let h := lsh.hRfits
    let b' := applyLadderStep lsh
    ∀ p, (∃ k, b' p = some ⟨.White, k⟩) →
         p = kingPos rank h ∨
         p = rookBPos rank .moveK h ∨
         p = rookAPos rank .moveK h := by
  obtain ⟨hK, hRb, hRa⟩ := applyLadderStep_PiecesAt_moveRa lsh
  exact Q_of_subset_card_le _ .White
    ⟨.King, hK⟩ ⟨.Rook, hRb⟩ ⟨.Rook, hRa⟩
    (ladderPos_pairwise_distinct rank .moveK lsh.hRfits)
    (whiteCount_le_three_after_step lsh)

lemma applyLadderStep_QPart_moveK {n : Nat} {board : Board n} {rank : Fin n}
    (lsh : LadderShape board rank .moveK) (hRoom : rank.val + 3 < n) :
    let rank' : Fin n := ⟨rank.val + 1, by omega⟩
    let h' : rank'.val + 2 < n := hRoom
    let b' := applyLadderStep lsh
    ∀ p, (∃ k, b' p = some ⟨.White, k⟩) →
         p = kingPos rank' h' ∨
         p = rookBPos rank' .moveRb h' ∨
         p = rookAPos rank' .moveRb h' := by
  obtain ⟨hK, hRb, hRa⟩ := applyLadderStep_PiecesAt_moveK lsh hRoom
  exact Q_of_subset_card_le _ .White
    ⟨.King, hK⟩ ⟨.Rook, hRb⟩ ⟨.Rook, hRa⟩
    (ladderPos_pairwise_distinct ⟨rank.val + 1, by omega⟩ .moveRb hRoom)
    (whiteCount_le_three_after_step lsh)
