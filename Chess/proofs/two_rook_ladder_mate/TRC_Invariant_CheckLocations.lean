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
  intro p k hpf hpr hp
  cases φ with
  | moveRb =>
    rcases applyLadderStep_QPart_moveRb lsh p ⟨k, hp⟩ with hp_eq | hp_eq | hp_eq
    · have : p.file.val = 0 := by rw [hp_eq]; simp [kingPos]
      omega
    · have : p.rank.val = rank.val + 1 := by rw [hp_eq]; simp [rookBPos]
      omega
    · have : p.file.val = 0 := by rw [hp_eq]; simp [rookAPos]
      omega
  | moveRa =>
    rcases applyLadderStep_QPart_moveRa lsh p ⟨k, hp⟩ with hp_eq | hp_eq | hp_eq
    · have : p.file.val = 0 := by rw [hp_eq]; simp [kingPos]
      omega
    · have : p.rank.val = rank.val + 1 := by rw [hp_eq]; simp [rookBPos]
      omega
    · have : p.file.val = 0 := by rw [hp_eq]; simp [rookAPos]
      omega
  | moveK =>
    have hRoom := lsh.moveK_hRoom
    rcases applyLadderStep_QPart_moveK lsh hRoom p ⟨k, hp⟩ with hp_eq | hp_eq | hp_eq
    · have : p.file.val = 0 := by rw [hp_eq]; simp [kingPos]
      omega
    · have : p.rank.val = rank.val + 1 := by rw [hp_eq]; simp [rookBPos]
      omega
    · have : p.file.val = 0 := by rw [hp_eq]; simp [rookAPos]
      omega

-- (2) Phase moveK (K → Rb): after the king's ply, no white piece sits
-- to the right of the post-step Ra rook. Post-step Ra is at (rank+2, 0);
-- the only white pieces sit at file 0 (K, Ra) or file 1 with rank rank+1
-- (Rb), none on rank rank+2 with file > 0.
lemma LadderMove_NoWhiteRightOfRa_moveK {n : Nat} {board : Board n}
    {rank : Fin n} (lsh : LadderShape board rank .moveK) :
    ∀ p k, p.rank.val = rank.val + 2 → 0 < p.file.val →
           (applyLadderStep lsh) p ≠ some ⟨.White, k⟩ := by
  intro p k hpr hpf hp
  have hRoom := lsh.moveK_hRoom
  rcases applyLadderStep_QPart_moveK lsh hRoom p ⟨k, hp⟩ with hp_eq | hp_eq | hp_eq
  · have : p.rank.val = rank.val + 1 := by rw [hp_eq]; simp [kingPos]
    omega
  · have : p.rank.val = rank.val + 1 := by rw [hp_eq]; simp [rookBPos]
    omega
  · have : p.file.val = 0 := by rw [hp_eq]; simp [rookAPos]
    omega

-- (3) Phase moveRb (Rb → Ra): after Rb's ply, no white piece sits to
-- the right of the post-step Rb rook. Post-step Rb is at (rank+1, 1);
-- the only piece sharing rank rank+1 is Ra at file 0 (left of Rb, not
-- right).
lemma LadderMove_NoWhiteRightOfRb_moveRb {n : Nat} {board : Board n}
    {rank : Fin n} (lsh : LadderShape board rank .moveRb) :
    ∀ p k, p.rank.val = rank.val + 1 → 1 < p.file.val →
           (applyLadderStep lsh) p ≠ some ⟨.White, k⟩ := by
  intro p k hpr hpf hp
  rcases applyLadderStep_QPart_moveRb lsh p ⟨k, hp⟩ with hp_eq | hp_eq | hp_eq
  · have : p.rank.val = rank.val := by rw [hp_eq]; simp [kingPos]
    omega
  · have : p.file.val = 1 := by rw [hp_eq]; simp [rookBPos]
    omega
  · have : p.file.val = 0 := by rw [hp_eq]; simp [rookAPos]
    omega

-- (4) Phase moveRa (Ra → K): after Ra's ply, no white piece sits to
-- the right of the post-step Ra rook. Post-step Ra is at (rank+2, 0);
-- no other white piece shares rank rank+2 (K at rank, Rb at rank+1).
lemma LadderMove_NoWhiteRightOfRa_moveRa {n : Nat} {board : Board n}
    {rank : Fin n} (lsh : LadderShape board rank .moveRa) :
    ∀ p k, p.rank.val = rank.val + 2 → 0 < p.file.val →
           (applyLadderStep lsh) p ≠ some ⟨.White, k⟩ := by
  intro p k hpr hpf hp
  rcases applyLadderStep_QPart_moveRa lsh p ⟨k, hp⟩ with hp_eq | hp_eq | hp_eq
  · have : p.rank.val = rank.val := by rw [hp_eq]; simp [kingPos]
    omega
  · have : p.rank.val = rank.val + 1 := by rw [hp_eq]; simp [rookBPos]
    omega
  · have : p.file.val = 0 := by rw [hp_eq]; simp [rookAPos]
    omega

-- (5) Phase moveRa (Ra → K): after Ra's ply, no white piece sits to
-- the right of the post-step Rb rook. Post-step Rb is at (rank+1, 1);
-- the only piece sharing rank rank+1 is Rb itself (the K and Ra sit on
-- ranks rank and rank+2 respectively).
lemma LadderMove_NoWhiteRightOfRb_moveRa {n : Nat} {board : Board n}
    {rank : Fin n} (lsh : LadderShape board rank .moveRa) :
    ∀ p k, p.rank.val = rank.val + 1 → 1 < p.file.val →
           (applyLadderStep lsh) p ≠ some ⟨.White, k⟩ := by
  intro p k hpr hpf hp
  rcases applyLadderStep_QPart_moveRa lsh p ⟨k, hp⟩ with hp_eq | hp_eq | hp_eq
  · have : p.rank.val = rank.val := by rw [hp_eq]; simp [kingPos]
    omega
  · have : p.file.val = 1 := by rw [hp_eq]; simp [rookBPos]
    omega
  · have : p.rank.val = rank.val + 2 := by rw [hp_eq]; simp [rookAPos]
    omega


-- ============================================================
-- ROOK ATTACKER WITNESSES ON THE STEP BOARD
-- ============================================================
-- Each lemma below packages, for one of the three "exclusion regions"
-- targeted by the ladder, a step-board rook witness suitable for
-- `RookCheckUp` / `RookCheckRight`:
--   • the rook position `rp` (with white rook on the step board)
--   • the rank/file value of `rp`
--   • a "no white piece in the attack region" line-of-sight predicate,
--     in the form expected by `RookCheckUp` / `RookCheckRight`.
--
-- These witnesses are board-agnostic in the sense that they don't fix
-- where the black king is — they just describe the rook configuration
-- on the step board. Two consumers use them:
--   1. `LadderMove_BlackInCheck_*` (below): apply the witness on the
--      step board with the actual king position to conclude
--      `IsCheck (applyLadderStep lsh) .Black`.
--   2. `BlackReply_Not*` (in `TRC_Invariant_KingRank.lean`): lift the
--      witness across the legal Black reply (rook stays put and white-
--      free regions stay white-free) and conclude
--      `IsCheck (applyMove ... bsrc bdst) .Black`, contradicting
--      `IsLegalSetup` of the post-black-move board.

-- The post-step Rb at (rank+1, 1) attacks vertically up file 1.
-- Phase-uniform because Rb sits at (rank+1, 1) after every White ply;
-- line of sight is from `LadderMove_NoWhiteAboveRb`.
lemma LadderMove_RookAttacker_AboveRaRank_FileOne {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ) :
    ∃ rp : Pos n,
      (applyLadderStep lsh) rp = some ⟨.White, .Rook⟩ ∧
      rp.rank.val = rank.val + 1 ∧
      rp.file.val = 1 ∧
      (∀ p k, p.file = rp.file → rp.rank.val < p.rank.val →
              (applyLadderStep lsh) p ≠ some ⟨.White, k⟩) := by
  -- A uniform witness for the post-step Rb position. Rb sits at
  -- (rank+1, 1) on every phase's step board, but the formal name of
  -- that square is phase-dependent.
  have h_witness :
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
  obtain ⟨rp, hRb_at, hRb_rank, hRb_file⟩ := h_witness
  refine ⟨rp, hRb_at, hRb_rank, hRb_file, ?_⟩
  intro p k hpf hpr
  apply LadderMove_NoWhiteAboveRb lsh p k
  · have := congrArg Fin.val hpf; rw [hRb_file] at this; exact this
  · rw [hRb_rank] at hpr; exact hpr

-- A rook on the step board sitting at Ra.rank with file < 2 attacks
-- horizontally rightward over file ≥ 2. The attacker differs by phase:
--   moveRb: Rb at (rank+1, 1) on rank+1 = Ra.rank.
--   moveRa: Rb at (rank+1, 1) on rank+1 = Ra.rank.
--   moveK : Ra at (rank+2, 0) on rank+2 = Ra.rank.
lemma LadderMove_RookAttacker_AtRaRank_FileGe2 {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ) :
    ∃ rp : Pos n,
      (applyLadderStep lsh) rp = some ⟨.White, .Rook⟩ ∧
      rp.rank.val = (rookAPos rank φ lsh.hRfits).rank.val ∧
      rp.file.val < 2 ∧
      (∀ p k, p.rank = rp.rank → rp.file.val < p.file.val →
              (applyLadderStep lsh) p ≠ some ⟨.White, k⟩) := by
  cases φ with
  | moveRb =>
    refine ⟨rookBPos rank .moveRa lsh.hRfits, ?_, ?_, ?_, ?_⟩
    · exact (applyLadderStep_PiecesAt_moveRb lsh).2.1
    · simp [rookBPos, rookAPos]
    · simp [rookBPos]
    · intro p k hpr hpf
      apply LadderMove_NoWhiteRightOfRb_moveRb lsh p k
      · have := congrArg Fin.val hpr; simp [rookBPos] at this; exact this
      · simp [rookBPos] at hpf; exact hpf
  | moveRa =>
    refine ⟨rookBPos rank .moveK lsh.hRfits, ?_, ?_, ?_, ?_⟩
    · exact (applyLadderStep_PiecesAt_moveRa lsh).2.1
    · simp [rookBPos, rookAPos]
    · simp [rookBPos]
    · intro p k hpr hpf
      apply LadderMove_NoWhiteRightOfRb_moveRa lsh p k
      · have := congrArg Fin.val hpr; simp [rookBPos] at this; exact this
      · simp [rookBPos] at hpf; exact hpf
  | moveK =>
    have hRoom := lsh.moveK_hRoom
    refine ⟨rookAPos ⟨rank.val + 1, by omega⟩ .moveRb hRoom, ?_, ?_, ?_, ?_⟩
    · exact (applyLadderStep_PiecesAt_moveK lsh hRoom).2.2
    · simp [rookAPos]
    · simp [rookAPos]
    · intro p k hpr hpf
      apply LadderMove_NoWhiteRightOfRa_moveK lsh p k
      · have := congrArg Fin.val hpr; simp [rookAPos] at this; exact this
      · simp [rookAPos] at hpf; exact hpf

-- Phase moveRa only: the post-step Ra sits at (rank+2, 0) =
-- (Ra.rank + 1, 0) and attacks horizontally rightward over that rank.
-- Line of sight is from `LadderMove_NoWhiteRightOfRa_moveRa`.
lemma LadderMove_RookAttacker_AtRaRankPlusOne_FileGe2_moveRa
    {n : Nat} {board : Board n} {rank : Fin n}
    (lsh : LadderShape board rank .moveRa) :
    ∃ rp : Pos n,
      (applyLadderStep lsh) rp = some ⟨.White, .Rook⟩ ∧
      rp.rank.val = (rookAPos rank .moveRa lsh.hRfits).rank.val + 1 ∧
      rp.file.val = 0 ∧
      (∀ p k, p.rank = rp.rank → rp.file.val < p.file.val →
              (applyLadderStep lsh) p ≠ some ⟨.White, k⟩) := by
  refine ⟨rookAPos rank .moveK lsh.hRfits, ?_, ?_, ?_, ?_⟩
  · exact (applyLadderStep_PiecesAt_moveRa lsh).2.2
  · simp [rookAPos]
  · simp [rookAPos]
  · intro p k hpr hpf
    apply LadderMove_NoWhiteRightOfRa_moveRa lsh p k
    · have := congrArg Fin.val hpr; simp [rookAPos] at this; exact this
    · simp [rookAPos] at hpf; exact hpf

-- ============================================================
-- BLACK-KING-IN-CHECK REGIONS ON THE STEP BOARD
-- ============================================================
-- For each black king location below, the post-step board has Black in
-- check. `Ra.rank` throughout refers to the *pre-move* rank of the Ra
-- rook, i.e. `(rookAPos rank φ lsh.hRfits).rank`. Each lemma is a thin
-- wrapper that combines the corresponding `LadderMove_RookAttacker_*`
-- witness above with `RookCheckUp` / `RookCheckRight` to produce the
-- step-board `IsCheck` conclusion.

-- (any phase) On the step board, a black king at (rank = Ra.rank,
-- file ≥ 2) is in check.
lemma LadderMove_BlackInCheck_AtRaRank_FileGe2 {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ) :
    ∀ kp, (applyLadderStep lsh) kp = some ⟨.Black, .King⟩ →
          kp.rank.val = (rookAPos rank φ lsh.hRfits).rank.val →
          2 ≤ kp.file.val →
          IsCheck (applyLadderStep lsh) .Black := by
  intro kp hkp hkp_rank hkp_file
  obtain ⟨rp, hRook_at, hrp_rank, hrp_file_lt, no_white_right⟩ :=
    LadderMove_RookAttacker_AtRaRank_FileGe2 lsh
  have only_bk := LadderMove_PreservesOnlyBlackKing lsh
  obtain ⟨_, _, _, _, h_step_legal⟩ := ladderStep_isLegal lsh
  obtain ⟨_, ⟨_, _, hbk_uniq⟩, _⟩ := h_step_legal
  have unique_bk : ∀ p,
      (applyLadderStep lsh) p = some ⟨.Black, .King⟩ → p = kp := fun p hp =>
    (hbk_uniq p hp).trans (hbk_uniq kp hkp).symm
  have same_rank : kp.rank = rp.rank := by
    apply Fin.ext; rw [hrp_rank]; exact hkp_rank
  have king_right : rp.file.val < kp.file.val := by omega
  exact RookCheckRight (applyLadderStep lsh) rp kp hRook_at hkp only_bk
    unique_bk no_white_right same_rank king_right

-- (any phase) On the step board, a black king at (file = 1,
-- rank > Ra.rank) is in check.
lemma LadderMove_BlackInCheck_AboveRaRank_FileOne {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ) :
    ∀ kp, (applyLadderStep lsh) kp = some ⟨.Black, .King⟩ →
          kp.file.val = 1 →
          (rookAPos rank φ lsh.hRfits).rank.val < kp.rank.val →
          IsCheck (applyLadderStep lsh) .Black := by
  intro kp hkp hkp_file hkp_rank
  obtain ⟨rp, hRb_at, hRb_rank, hRb_file, no_white_above⟩ :=
    LadderMove_RookAttacker_AboveRaRank_FileOne lsh
  have hpreRa_rank_ge :
      rank.val + 1 ≤ (rookAPos rank φ lsh.hRfits).rank.val := by
    cases φ <;> simp [rookAPos]
  have only_bk := LadderMove_PreservesOnlyBlackKing lsh
  obtain ⟨_, _, _, _, h_step_legal⟩ := ladderStep_isLegal lsh
  obtain ⟨_, ⟨_, _, hbk_uniq⟩, _⟩ := h_step_legal
  have unique_bk : ∀ p,
      (applyLadderStep lsh) p = some ⟨.Black, .King⟩ → p = kp := fun p hp =>
    (hbk_uniq p hp).trans (hbk_uniq kp hkp).symm
  have same_file : kp.file = rp.file := by
    apply Fin.ext; rw [hRb_file]; exact hkp_file
  have king_above : rp.rank.val < kp.rank.val := by
    rw [hRb_rank]; omega
  exact RookCheckUp (applyLadderStep lsh) rp kp hRb_at hkp only_bk unique_bk
    no_white_above same_file king_above

-- Phase moveRa (Ra → K): on the step board, a black king at
-- (rank = Ra.rank + 1, file ≥ 2) is in check.
lemma LadderMove_BlackInCheck_AtRaRankPlusOne_FileGe2_moveRa
    {n : Nat} {board : Board n} {rank : Fin n}
    (lsh : LadderShape board rank .moveRa) :
    ∀ kp, (applyLadderStep lsh) kp = some ⟨.Black, .King⟩ →
          kp.rank.val = (rookAPos rank .moveRa lsh.hRfits).rank.val + 1 →
          2 ≤ kp.file.val →
          IsCheck (applyLadderStep lsh) .Black := by
  intro kp hkp hkp_rank hkp_file
  obtain ⟨rp, hRa_at, hrp_rank, hrp_file, no_white_right⟩ :=
    LadderMove_RookAttacker_AtRaRankPlusOne_FileGe2_moveRa lsh
  have only_bk := LadderMove_PreservesOnlyBlackKing lsh
  obtain ⟨_, _, _, _, h_step_legal⟩ := ladderStep_isLegal lsh
  obtain ⟨_, ⟨_, _, hbk_uniq⟩, _⟩ := h_step_legal
  have unique_bk : ∀ p,
      (applyLadderStep lsh) p = some ⟨.Black, .King⟩ → p = kp := fun p hp =>
    (hbk_uniq p hp).trans (hbk_uniq kp hkp).symm
  have same_rank : kp.rank = rp.rank := by
    apply Fin.ext; rw [hkp_rank, hrp_rank]
  have king_right : rp.file.val < kp.file.val := by
    rw [hrp_file]; omega
  exact RookCheckRight (applyLadderStep lsh) rp kp hRa_at hkp only_bk
    unique_bk no_white_right same_rank king_right
