import ChessRules
import TRC_FunctionWithInvariant
import TRC_Invariant_PieceLocations
import TRC_Q_Lemma

-- ============================================================
-- WHITE-PIECE-FREE REGIONS ON THE STEP BOARD
-- ============================================================
-- A board satisfying `LadderShape board rank φ` is modified by a single
-- White ply (`applyLadderStep`). The lemmas below pin down regions of the
-- step board that contain no white piece. They feed into the `RookCheckUp`
-- / `RookCheckRight` rook-check helpers in `HelperLemmas.lean` to
-- conclude that specific squares attacked by Rb or Ra are off-limits for
-- a legal Black king reply.
--
-- Post-step white piece positions (from `applyLadderStep_PiecesAt_*`):
--   input φ        K              Rb              Ra
--   moveRb         (R, 0)         (R+1, 1)        (R+1, 0)
--   moveRa         (R, 0)         (R+1, 1)        (R+2, 0)
--   moveK          (R+1, 0)       (R+1, 1)        (R+2, 0)
-- The post-step Rb is always at (R+1, 1), which is why "no white above
-- Rb" is phase-uniform; the post-step Ra differs between input phases,
-- so the Ra-right lemmas are split by phase.

-- (1) After White's ply (any input phase), no white piece sits above the
-- post-step Rb rook (file = 1, rank > rank+1). Phase-uniform because Rb's
-- post-step square is (rank+1, 1) in every phase.
lemma LadderMove_NoWhiteAboveRb {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ) :
    ∀ p k, p.file.val = 1 → rank.val + 1 < p.rank.val →
           (applyLadderStep lsh) p ≠ some ⟨.White, k⟩ := by
  sorry

-- (2) Phase moveK (K → Rb): after the king's ply, no white piece sits
-- to the right of the post-step Ra rook. Post-step Ra is at (rank+2, 0);
-- the only white pieces sit at file 0 (K, Ra) or file 1 with rank rank+1
-- (Rb), none on rank rank+2 with file > 0.
lemma LadderMove_NoWhiteRightOfRa_moveK {n : Nat} {board : Board n}
    {rank : Fin n} (lsh : LadderShape board rank .moveK) :
    ∀ p k, p.rank.val = rank.val + 2 → 0 < p.file.val →
           (applyLadderStep lsh) p ≠ some ⟨.White, k⟩ := by
  sorry

-- (3) Phase moveRb (Rb → Ra): after Rb's ply, no white piece sits to
-- the right of the post-step Rb rook. Post-step Rb is at (rank+1, 1);
-- the only piece sharing rank rank+1 is Ra at file 0 (left of Rb, not
-- right).
lemma LadderMove_NoWhiteRightOfRb_moveRb {n : Nat} {board : Board n}
    {rank : Fin n} (lsh : LadderShape board rank .moveRb) :
    ∀ p k, p.rank.val = rank.val + 1 → 1 < p.file.val →
           (applyLadderStep lsh) p ≠ some ⟨.White, k⟩ := by
  sorry

-- (4) Phase moveRa (Ra → K): after Ra's ply, no white piece sits to
-- the right of the post-step Ra rook. Post-step Ra is at (rank+2, 0);
-- no other white piece shares rank rank+2 (K at rank, Rb at rank+1).
lemma LadderMove_NoWhiteRightOfRa_moveRa {n : Nat} {board : Board n}
    {rank : Fin n} (lsh : LadderShape board rank .moveRa) :
    ∀ p k, p.rank.val = rank.val + 2 → 0 < p.file.val →
           (applyLadderStep lsh) p ≠ some ⟨.White, k⟩ := by
  sorry

-- (5) Phase moveRa (Ra → K): after Ra's ply, no white piece sits to
-- the right of the post-step Rb rook. Post-step Rb is at (rank+1, 1);
-- the only piece sharing rank rank+1 is Rb itself (the K and Ra sit on
-- ranks rank and rank+2 respectively).
lemma LadderMove_NoWhiteRightOfRb_moveRa {n : Nat} {board : Board n}
    {rank : Fin n} (lsh : LadderShape board rank .moveRa) :
    ∀ p k, p.rank.val = rank.val + 1 → 1 < p.file.val →
           (applyLadderStep lsh) p ≠ some ⟨.White, k⟩ := by
  sorry


-- ============================================================
-- BLACK-KING-IN-CHECK REGIONS ON THE STEP BOARD
-- ============================================================
-- For each black king location below, the post-step board has Black in
-- check. `Ra.rank` throughout refers to the *pre-move* rank of the Ra
-- rook, i.e. `(rookAPos rank φ lsh.hRfits).rank`. The witnessing attacker
-- is either Rb or Ra on the step board, depending on the phase; the no-
-- white-region lemmas (1)–(5) above supply the line-of-sight condition,
-- and the `RookCheckUp` / `RookCheckRight` helpers in
-- `HelperLemmas.lean` close out the check.

-- (any phase) On the step board, a black king at (rank = Ra.rank,
-- file ≥ 2) is in check. Phase-by-phase the attacker differs:
--   moveRb: Rb at (rank+1, 1) attacks horizontally on rank+1 = Ra.rank.
--   moveRa: Rb at (rank+1, 1) attacks horizontally on rank+1 = Ra.rank.
--   moveK : Ra at (rank+2, 0) attacks horizontally on rank+2 = Ra.rank.
lemma LadderMove_BlackInCheck_AtRaRank_FileGe2 {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ) :
    ∀ kp, (applyLadderStep lsh) kp = some ⟨.Black, .King⟩ →
          kp.rank.val = (rookAPos rank φ lsh.hRfits).rank.val →
          2 ≤ kp.file.val →
          IsCheck (applyLadderStep lsh) .Black := by
  sorry

-- (any phase) On the step board, a black king at (file = 1,
-- rank > Ra.rank) is in check. The post-step Rb sits at (rank+1, 1) in
-- every phase, and Ra.rank ≥ rank+1, so the king's rank is strictly
-- above Rb's rank; Rb attacks vertically on file 1. Line of sight is
-- secured by `LadderMove_NoWhiteAboveRb`.
lemma LadderMove_BlackInCheck_AboveRaRank_FileOne {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ) :
    ∀ kp, (applyLadderStep lsh) kp = some ⟨.Black, .King⟩ →
          kp.file.val = 1 →
          (rookAPos rank φ lsh.hRfits).rank.val < kp.rank.val →
          IsCheck (applyLadderStep lsh) .Black := by
  intro kp hkp hkp_file hkp_rank
  -- A uniform witness for the post-step Rb position. In every phase Rb
  -- sits at (rank+1, 1) on the step board, but the formal name of that
  -- square is phase-dependent — so we package it once here.
  obtain ⟨rp, hRb_at, hRb_rank, hRb_file⟩ :
      ∃ rp : Pos n,
        (applyLadderStep lsh) rp = some ⟨.White, .Rook⟩ ∧
        rp.rank.val = rank.val + 1 ∧
        rp.file.val = 1 := by
    cases φ with
    | moveRb =>
      refine ⟨rookBPos rank .moveRa lsh.hRfits, ?_, ?_, ?_⟩
      · exact (applyLadderStep_PiecesAt_moveRb lsh).2.1
      · simp [rookBPos]
      · simp [rookBPos]
    | moveRa =>
      refine ⟨rookBPos rank .moveK lsh.hRfits, ?_, ?_, ?_⟩
      · exact (applyLadderStep_PiecesAt_moveRa lsh).2.1
      · simp [rookBPos]
      · simp [rookBPos]
    | moveK =>
      have hRoom := lsh.moveK_hRoom
      refine ⟨rookBPos ⟨rank.val + 1, by omega⟩ .moveRb hRoom, ?_, ?_, ?_⟩
      · exact (applyLadderStep_PiecesAt_moveK lsh hRoom).2.1
      · simp [rookBPos]
      · simp [rookBPos]
  have hpreRa_rank_ge :
      rank.val + 1 ≤ (rookAPos rank φ lsh.hRfits).rank.val := by
    cases φ <;> simp [rookAPos]
  have only_bk := LadderMove_PreservesOnlyBlackKing lsh
  obtain ⟨_, _, _, _, h_step_legal⟩ := ladderStep_isLegal lsh
  obtain ⟨_, ⟨_, _, hbk_uniq⟩, _⟩ := h_step_legal
  have unique_bk : ∀ p,
      (applyLadderStep lsh) p = some ⟨.Black, .King⟩ → p = kp := fun p hp =>
    (hbk_uniq p hp).trans (hbk_uniq kp hkp).symm
  have no_white_above :
      ∀ p k, p.file = rp.file → rp.rank.val < p.rank.val →
             (applyLadderStep lsh) p ≠ some ⟨.White, k⟩ := by
    intro p k hpf hpr
    apply LadderMove_NoWhiteAboveRb lsh p k
    · have := congrArg Fin.val hpf; rw [hRb_file] at this; exact this
    · rw [hRb_rank] at hpr; exact hpr
  have same_file : kp.file = rp.file := by
    apply Fin.ext; rw [hRb_file]; exact hkp_file
  have king_above : rp.rank.val < kp.rank.val := by
    rw [hRb_rank]; omega
  exact RookCheckUp (applyLadderStep lsh) rp kp hRb_at hkp only_bk unique_bk
    no_white_above same_file king_above

-- Phase moveRa (Ra → K): on the step board, a black king at
-- (rank = Ra.rank + 1, file ≥ 2) is in check. Post-step Ra sits at
-- (rank+2, 0) = (Ra.rank + 1, 0); it attacks horizontally rightward on
-- that rank, and `LadderMove_NoWhiteRightOfRa_moveRa` clears the line.
lemma LadderMove_BlackInCheck_AtRaRankPlusOne_FileGe2_moveRa
    {n : Nat} {board : Board n} {rank : Fin n}
    (lsh : LadderShape board rank .moveRa) :
    ∀ kp, (applyLadderStep lsh) kp = some ⟨.Black, .King⟩ →
          kp.rank.val = (rookAPos rank .moveRa lsh.hRfits).rank.val + 1 →
          2 ≤ kp.file.val →
          IsCheck (applyLadderStep lsh) .Black := by
  intro kp hkp hkp_rank hkp_file
  obtain ⟨_, _, hRa_at⟩ := applyLadderStep_PiecesAt_moveRa lsh
  have hRa_rank : (rookAPos rank .moveK lsh.hRfits).rank.val = rank.val + 2 := by
    simp [rookAPos]
  have hRa_file : (rookAPos rank .moveK lsh.hRfits).file.val = 0 := by
    simp [rookAPos]
  have hpreRa_rank : (rookAPos rank .moveRa lsh.hRfits).rank.val = rank.val + 1 := by
    simp [rookAPos]
  have only_bk := LadderMove_PreservesOnlyBlackKing lsh
  obtain ⟨_, _, _, _, h_step_legal⟩ := ladderStep_isLegal lsh
  obtain ⟨_, ⟨_, _, hbk_uniq⟩, _⟩ := h_step_legal
  have unique_bk : ∀ p,
      (applyLadderStep lsh) p = some ⟨.Black, .King⟩ → p = kp := fun p hp =>
    (hbk_uniq p hp).trans (hbk_uniq kp hkp).symm
  have no_white_right :
      ∀ p k, p.rank = (rookAPos rank .moveK lsh.hRfits).rank →
             (rookAPos rank .moveK lsh.hRfits).file.val < p.file.val →
             (applyLadderStep lsh) p ≠ some ⟨.White, k⟩ := by
    intro p k hpr hpf
    apply LadderMove_NoWhiteRightOfRa_moveRa lsh p k
    · have := congrArg Fin.val hpr; omega
    · rw [hRa_file] at hpf; exact hpf
  have same_rank :
      kp.rank = (rookAPos rank .moveK lsh.hRfits).rank := by
    apply Fin.ext; rw [hkp_rank]; omega
  have king_right :
      (rookAPos rank .moveK lsh.hRfits).file.val < kp.file.val := by
    rw [hRa_file]; omega
  exact RookCheckRight (applyLadderStep lsh)
    (rookAPos rank .moveK lsh.hRfits) kp
    hRa_at hkp only_bk unique_bk no_white_right same_rank king_right
