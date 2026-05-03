import ChessRules
import TRC_FunctionWithInvariant
import TRC_Invariant_PieceLocations
import TRC_Q_Lemma

-- ------------------------------------------------------------
-- BLACK REPLY TARGETS AN EMPTY SQUARE
-- ------------------------------------------------------------
-- Closes the `bdst_empty` hypothesis used inside `LadderShape.preservation`
-- (currently `sorry`'d). The argument chains four facts about the step
-- board (the board after White's ladder ply):
--
--   (i)   The (unique) black king still has file ≥ 2 and rank strictly
--         greater than `rookAPos rank φ` — White's ply moves into an
--         empty square (`LadderMove_IntoEmptySquare`), so it doesn't
--         relocate the black king, and the file/rank bounds carry over
--         from `LadderShape_KingsApart` and the `black_loc` conjunct.
--   (ii)  A legal Black king reply moves at most one square in each
--         coordinate, so its destination has file ≥ 1 and
--         rank ≥ rookAPos.rank.
--   (iii) The square at (file = 1, rank = rookAPos.rank) is attacked
--         by the White king on the step board in every phase, so a
--         legal Black reply cannot land there (it would leave Black
--         in check).
--   (iv)  The only White piece on the step board sitting at
--         (file ≥ 1, rank ≥ rookAPos.rank) is at (file = 1,
--         rank = rookAPos.rank). For phases moveRb / moveRa this is
--         the post-step rookB square; for phase moveK no white piece
--         lies in the region at all (vacuous). Proving this needs Q
--         transported through White's ply (via the same
--         `colorSquares_card_eq_nonCapture` /  `Q_of_subset_card_le`
--         machinery used by `whiteCount_le_three_after_cycle`).
--
-- (ii)+(iii)+(iv) together say `bdst` carries no white piece on the
-- step board; combined with "only black piece is the king, sitting at
-- bsrc ≠ bdst", this gives `bdst` is empty.

-- (i) The black king's square on the step board has file ≥ 2 and
-- rank > rookAPos.rank.
lemma LadderMove_BlackKing_FarFromRa {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ) :
    ∀ bp, (applyLadderStep lsh) bp = some ⟨.Black, .King⟩ →
          2 ≤ bp.file.val ∧
          (rookAPos rank φ lsh.hRfits).rank.val < bp.rank.val := by
  intro bp hbp
  obtain ⟨_, hK_at, hRb_at, hRa_at, _, black_loc, _, _⟩ := lsh.unfold
  -- The white move's source carries some white piece (Rook in moveRb /
  -- moveRa, King in moveK), and its destination is empty
  -- (`LadderMove_IntoEmptySquare`). So bp can be neither src nor dst —
  -- the black king at bp on the step board is already at bp on the
  -- original board.
  have hbp' : (applyMove board (ladderStep lsh).1 (ladderStep lsh).2) bp
              = some ⟨.Black, .King⟩ := hbp
  rw [applyMove_pieces] at hbp'
  have h_src_white :
      ∃ k, board (ladderStep lsh).1 = some ⟨.White, k⟩ := by
    cases φ
    · exact ⟨.Rook, hRb_at⟩
    · exact ⟨.Rook, hRa_at⟩
    · exact ⟨.King, hK_at⟩
  have hbp_orig : board bp = some ⟨.Black, .King⟩ := by
    by_cases h1 : bp = (ladderStep lsh).2
    · rw [if_pos h1] at hbp'
      obtain ⟨_, hk⟩ := h_src_white
      rw [hk] at hbp'; simp at hbp'
    · rw [if_neg h1] at hbp'
      by_cases h2 : bp = (ladderStep lsh).1
      · rw [if_pos h2] at hbp'; simp at hbp'
      · rw [if_neg h2] at hbp'; exact hbp'
  exact ⟨LadderShape_KingsApart lsh bp hbp_orig, black_loc bp hbp_orig⟩

-- (ii) After any legal Black king reply on the step board, the
-- destination has file ≥ 1 and rank ≥ rookAPos.rank.
lemma BlackReply_DstBounds {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    1 ≤ bdst.file.val ∧
    (rookAPos rank φ lsh.hRfits).rank.val ≤ bdst.rank.val := by
  obtain ⟨turn_white, _⟩ := lsh.unfold
  -- The step board has Black to move (White's ply flips the turn).
  have h_turn : (applyLadderStep lsh).turn = .Black := by
    show board.turn.opponent = .Black
    rw [turn_white]; rfl
  -- Unpack IsLegalMove and pin the moving piece to .King via
  -- `LadderMove_PreservesOnlyBlackKing`.
  obtain ⟨piece, hat_src, h_valid, _, _⟩ := black_move
  rw [h_turn] at hat_src
  have hk : piece = .King :=
    LadderMove_PreservesOnlyBlackKing lsh bsrc piece hat_src
  subst hk
  -- bsrc inherits the BlackKing bounds; ValidKingMove gives WithinOne
  -- on each coordinate, so bdst is at most one square away.
  obtain ⟨h_bsrc_file, h_bsrc_rank⟩ :=
    LadderMove_BlackKing_FarFromRa lsh bsrc hat_src
  change ValidKingMove bsrc bdst at h_valid
  obtain ⟨_, h_rank, h_file⟩ := h_valid
  unfold WithinOne at h_rank h_file
  refine ⟨?_, ?_⟩
  · omega
  · omega

-- (iii) On the step board, the White king attacks the square at
-- (file = 1, rank = rookAPos.rank). Pure phase-by-phase check: the
-- White king sits one step diagonally below this square in moveRb /
-- moveRa, and one step left of it in moveK (after the King's own ply
-- has advanced by one rank).
lemma LadderMove_WhiteKingAttacks_FileOneRaRank {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ) :
    ∀ wk q, (applyLadderStep lsh) wk = some ⟨.White, .King⟩ →
            q.file.val = 1 →
            q.rank.val = (rookAPos rank φ lsh.hRfits).rank.val →
            ValidKingMove wk q := by
  intro wk q hwk hqfile hqrank
  cases φ with
  | moveRb =>
    obtain ⟨_, hRb_at, hRa_at⟩ := applyLadderStep_PiecesAt_moveRb lsh
    rcases applyLadderStep_QPart_moveRb lsh wk ⟨.King, hwk⟩ with hwk_eq | hwk_eq | hwk_eq
    · rw [hwk_eq]
      have hRa_rank : (rookAPos rank .moveRb lsh.hRfits).rank.val = rank.val + 1 := by
        simp [rookAPos]
      refine ⟨?_, ?_, ?_⟩
      · intro heq
        have := congrArg (·.file.val) heq
        simp [kingPos] at this; omega
      · unfold WithinOne; simp [kingPos]; omega
      · unfold WithinOne; simp [kingPos]; omega
    · rw [hwk_eq, hRb_at] at hwk; simp at hwk
    · rw [hwk_eq, hRa_at] at hwk; simp at hwk
  | moveRa =>
    obtain ⟨_, hRb_at, hRa_at⟩ := applyLadderStep_PiecesAt_moveRa lsh
    rcases applyLadderStep_QPart_moveRa lsh wk ⟨.King, hwk⟩ with hwk_eq | hwk_eq | hwk_eq
    · rw [hwk_eq]
      have hRa_rank : (rookAPos rank .moveRa lsh.hRfits).rank.val = rank.val + 1 := by
        simp [rookAPos]
      refine ⟨?_, ?_, ?_⟩
      · intro heq
        have := congrArg (·.file.val) heq
        simp [kingPos] at this; omega
      · unfold WithinOne; simp [kingPos]; omega
      · unfold WithinOne; simp [kingPos]; omega
    · rw [hwk_eq, hRb_at] at hwk; simp at hwk
    · rw [hwk_eq, hRa_at] at hwk; simp at hwk
  | moveK =>
    have hRoom := lsh.moveK_hRoom
    obtain ⟨_, hRb_at, hRa_at⟩ := applyLadderStep_PiecesAt_moveK lsh hRoom
    rcases applyLadderStep_QPart_moveK lsh hRoom wk ⟨.King, hwk⟩ with hwk_eq | hwk_eq | hwk_eq
    · rw [hwk_eq]
      have hRa_rank : (rookAPos rank .moveK lsh.hRfits).rank.val = rank.val + 2 := by
        simp [rookAPos]
      refine ⟨?_, ?_, ?_⟩
      · intro heq
        have := congrArg (·.file.val) heq
        simp [kingPos] at this; omega
      · unfold WithinOne; simp [kingPos]; omega
      · unfold WithinOne; simp [kingPos]; omega
    · rw [hwk_eq, hRb_at] at hwk; simp at hwk
    · rw [hwk_eq, hRa_at] at hwk; simp at hwk

-- Corollary of (iii): a legal Black reply cannot land on the
-- (file = 1, rank = rookAPos.rank) square — going there would leave
-- the Black king attacked by the protecting White king and thus
-- violate `IsLegalSetup` (¬ IsCheck Black) on the post-reply board.
lemma BlackReply_NotAtFileOneRaRank {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    ¬ (bdst.file.val = 1 ∧
       bdst.rank.val = (rookAPos rank φ lsh.hRfits).rank.val) := by
  rintro ⟨hfile, hrank⟩
  obtain ⟨piece, hat_src, h_valid, _, h_legal⟩ := black_move
  obtain ⟨turn_white, _⟩ := lsh.unfold
  have h_turn_step : (applyLadderStep lsh).turn = .Black := by
    show board.turn.opponent = .Black
    rw [turn_white]; rfl
  rw [h_turn_step] at hat_src
  have hk : piece = .King := LadderMove_PreservesOnlyBlackKing lsh bsrc piece hat_src
  subst hk
  change ValidKingMove bsrc bdst at h_valid
  -- Get a witness wk for the White king on the step board (per phase).
  have h_wk_exists : ∃ wk, (applyLadderStep lsh) wk = some ⟨.White, .King⟩ := by
    cases φ with
    | moveRb => exact ⟨_, (applyLadderStep_PiecesAt_moveRb lsh).1⟩
    | moveRa => exact ⟨_, (applyLadderStep_PiecesAt_moveRa lsh).1⟩
    | moveK  => exact ⟨_, (applyLadderStep_PiecesAt_moveK lsh lsh.moveK_hRoom).1⟩
  obtain ⟨wk, hwk_at⟩ := h_wk_exists
  -- The White king on the step board attacks bdst (the assumed square).
  have h_attack : ValidKingMove wk bdst :=
    LadderMove_WhiteKingAttacks_FileOneRaRank lsh wk bdst hwk_at hfile hrank
  -- wk ≠ bsrc: bsrc has the black king, wk has the white king.
  have h_wk_ne_bsrc : wk ≠ bsrc := by
    intro heq; subst heq
    rw [hat_src] at hwk_at; simp at hwk_at
  -- wk ≠ bdst: the first conjunct of `ValidKingMove`.
  have h_wk_ne_bdst : wk ≠ bdst := h_attack.1
  -- White king is preserved across the black move (wk is neither src nor dst).
  have hwk_on_b'' :
      (applyMove (applyLadderStep lsh) bsrc bdst) wk = some ⟨.White, .King⟩ := by
    rw [applyMove_pieces, if_neg h_wk_ne_bdst, if_neg h_wk_ne_bsrc]
    exact hwk_at
  -- Black king is at bdst on the post-reply board.
  have hb''_bdst :
      (applyMove (applyLadderStep lsh) bsrc bdst) bdst = some ⟨.Black, .King⟩ := by
    rw [applyMove_pieces, if_pos rfl]; exact hat_src
  -- The third conjunct of IsLegalSetup gives ¬ IsCheck on the side
  -- not to move; the post-reply turn is White, so its opponent is Black.
  obtain ⟨_, _, h_no_check⟩ := h_legal
  have h_b''_opp : (applyMove (applyLadderStep lsh) bsrc bdst).turn.opponent = .Black := by
    show (applyLadderStep lsh).turn.opponent.opponent = .Black
    rw [h_turn_step]; rfl
  rw [h_b''_opp] at h_no_check
  exact h_no_check ⟨bdst, hb''_bdst, wk, .inr ⟨hwk_on_b'', h_attack⟩⟩

-- (iv) On the step board, any White piece at file ≥ 1 and
-- rank ≥ rookAPos.rank sits at exactly (file = 1, rank = rookAPos.rank).
-- For moveRb / moveRa this is the (post-step) rookB square; for moveK
-- there is no White piece in the region at all, so the conclusion is
-- vacuous.
--
-- Note: the proof case-splits on φ and dispatches to the
-- corresponding `applyLadderStep_QPart_*` lemma (Q on the step board for
-- that phase) to enumerate the three candidate white squares.
lemma LadderMove_OnlyFileOneRaRank_InRegion {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ) :
    ∀ p, 1 ≤ p.file.val →
         (rookAPos rank φ lsh.hRfits).rank.val ≤ p.rank.val →
         (∃ k, (applyLadderStep lsh) p = some ⟨.White, k⟩) →
         p.file.val = 1 ∧
         p.rank.val = (rookAPos rank φ lsh.hRfits).rank.val := by
  intro p hfile hrank hwhite
  cases φ with
  | moveRb =>
    -- Post-step white pieces sit at (rank, 0), (rank+1, 1), (rank+1, 0).
    -- Only (rank+1, 1) has file ≥ 1 — the king's and rookA's files are 0.
    rcases applyLadderStep_QPart_moveRb lsh p hwhite with hp | hp | hp
    · rw [hp] at hfile; simp [kingPos] at hfile
    · rw [hp]; exact ⟨by simp [rookBPos], by simp [rookBPos, rookAPos]⟩
    · rw [hp] at hfile; simp [rookAPos] at hfile
  | moveRa =>
    -- Same shape as moveRb (Rb post-step is at the same square).
    rcases applyLadderStep_QPart_moveRa lsh p hwhite with hp | hp | hp
    · rw [hp] at hfile; simp [kingPos] at hfile
    · rw [hp]; exact ⟨by simp [rookBPos], by simp [rookBPos, rookAPos]⟩
    · rw [hp] at hfile; simp [rookAPos] at hfile
  | moveK =>
    -- Post-step white pieces at (rank+1, 0), (rank+1, 1), (rank+2, 0).
    -- The region is (file ≥ 1, rank ≥ rank+2): rookB has rank rank+1 (fails
    -- the rank bound), the king and rookA have file 0 (fail the file bound).
    -- So the conclusion is vacuously true.
    have hRoom := lsh.moveK_hRoom
    rcases applyLadderStep_QPart_moveK lsh hRoom p hwhite with hp | hp | hp
    · rw [hp] at hfile; simp [kingPos] at hfile
    · rw [hp] at hrank; simp [rookBPos, rookAPos] at hrank
    · rw [hp] at hfile; simp [rookAPos] at hfile

-- Corollary of (ii)+(iii)+(iv): a legal Black reply's destination
-- carries no white piece on the step board.
lemma BlackReply_DstNotWhite {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    ∀ k, (applyLadderStep lsh) bdst ≠ some ⟨.White, k⟩ := by
  intro k hk
  obtain ⟨h_file, h_rank⟩ := BlackReply_DstBounds lsh black_move
  have h_at :=
    LadderMove_OnlyFileOneRaRank_InRegion lsh bdst h_file h_rank ⟨k, hk⟩
  exact BlackReply_NotAtFileOneRaRank lsh black_move h_at

-- Final: the destination is empty on the step board. Combines
-- `BlackReply_DstNotWhite` with "any black piece on the step board is
-- the (unique) black king, which sits at bsrc ≠ bdst", to rule out
-- both colors at bdst.
lemma BlackReply_DstEmpty {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    (applyLadderStep lsh) bdst = none := by
  rcases hb : (applyLadderStep lsh) bdst with _ | ⟨c, k⟩
  · rfl
  · exfalso
    cases c with
    | White => exact BlackReply_DstNotWhite lsh black_move k hb
    | Black =>
      -- bdst would carry the (unique) black king. But bsrc also carries the
      -- black king (the moving piece). Uniqueness forces bsrc = bdst, which
      -- contradicts ValidKingMove's src ≠ dst.
      have hk : k = .King :=
        LadderMove_PreservesOnlyBlackKing lsh bdst k hb
      subst hk
      obtain ⟨piece, hat_src, h_valid, _, _⟩ := black_move
      obtain ⟨turn_white, _⟩ := lsh.unfold
      have h_turn_step : (applyLadderStep lsh).turn = .Black := by
        show board.turn.opponent = .Black
        rw [turn_white]; rfl
      rw [h_turn_step] at hat_src
      have hp : piece = .King :=
        LadderMove_PreservesOnlyBlackKing lsh bsrc piece hat_src
      subst hp
      change ValidKingMove bsrc bdst at h_valid
      obtain ⟨_, _, _, _, h_step_legal⟩ := ladderStep_isLegal lsh
      obtain ⟨_, ⟨_, _, h_uniq⟩, _⟩ := h_step_legal
      exact h_valid.1 ((h_uniq bsrc hat_src).trans (h_uniq bdst hb).symm)
