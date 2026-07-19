import ChessRules
import TRC_FunctionWithInvariant
import LadderStepIsLegal
import TRC_FinalState
import TRC_Invariant_BlackEmpty
import TRC_Q_Lemma
import HelperLemmas

-- ============================================================
-- BLACK HAS A LEGAL REPLY (UNLESS FINAL)
-- ============================================================
-- For any non-final ladder state on a board with room (`3 < n`), the
-- Black king has at least one legal destination after applyLadderStep.
--
-- The bound `3 < n` is necessary, not an artefact: on a 3×3 board the
-- ladder can stalemate Black in phase moveRb. See the `stuck3`
-- counterexample in `TRC_Tests.lean`.
--
-- ── Shape of the argument ──
-- After White's ply every white piece sits on file 0 or 1, at rank at
-- most `whiteTopRank` (below). So every square with file ≥ 2 and rank
-- above `whiteTopRank` is both empty and safe: no rook shares its rank
-- or file, and the white king — always on file 0 — is two files away.
-- The Black king already has file ≥ 2 and rank ≥ `whiteTopRank`
-- (`LadderMove_BlackKing_FarFromRa`), so either
--   • it is strictly above `whiteTopRank`, and any neighbour inside the
--     safe rectangle works (`IsLegalSetup.king_in_rect_has_legal_move`,
--     whose non-degeneracy side condition is where `3 < n` is used); or
--   • it sits exactly on `whiteTopRank` — only possible in phase moveRa,
--     where it is in check from rookA — and it retreats straight up,
--     which non-finality guarantees is on the board.


-- ------------------------------------------------------------
-- THE WHITE PIECES' RANK CEILING AFTER WHITE'S PLY
-- ------------------------------------------------------------
-- Post-step white squares, by input phase:
--   moveRb   K (R,0)    Rb (R+1,1)   Ra (R+1,0)   → ceiling R+1
--   moveRa   K (R,0)    Rb (R+1,1)   Ra (R+2,0)   → ceiling R+2
--   moveK    K (R+1,0)  Rb (R+1,1)   Ra (R+2,0)   → ceiling R+2
def whiteTopRank {n : Nat} (rank : Fin n) : LadderPhase → Nat
  | .moveRb => rank.val + 1
  | .moveRa => rank.val + 2
  | .moveK  => rank.val + 2

-- The ceiling brackets the pre-move rookA rank: at least it, and at
-- most one more. The lower bound puts the safe region inside the reach
-- of `LadderMove_OnlyFileOneRaRank_InRegion`; the upper bound turns
-- "black king strictly above pre-move rookA" into "black king at least
-- at the ceiling".
lemma preRa_le_whiteTopRank {n : Nat} (rank : Fin n) (φ : LadderPhase)
    (h : rank.val + 2 < n) :
    (rookAPos rank φ h).rank.val ≤ whiteTopRank rank φ ∧
    whiteTopRank rank φ ≤ (rookAPos rank φ h).rank.val + 1 := by
  cases φ <;> simp [rookAPos, whiteTopRank]

-- Every white piece on the step board is on file 0 or 1, at rank at
-- most the ceiling. Immediate from the step-board `Q` lemmas, which
-- enumerate the three white squares.
lemma stepBoard_WhiteConfined {n : Nat} {board : Board n} {rank : Fin n}
    {φ : LadderPhase} (lsh : LadderShape board rank φ) :
    ∀ p, (∃ k, (applyLadderStep lsh) p = some ⟨.White, k⟩) →
      p.file.val ≤ 1 ∧ p.rank.val ≤ whiteTopRank rank φ := by
  intro p hp
  cases φ with
  | moveRb =>
    rcases applyLadderStep_QPart_moveRb lsh p hp with h | h | h <;>
      subst h <;> simp [kingPos, rookBPos, rookAPos, whiteTopRank]
  | moveRa =>
    rcases applyLadderStep_QPart_moveRa lsh p hp with h | h | h <;>
      subst h <;> simp [kingPos, rookBPos, rookAPos, whiteTopRank]
  | moveK =>
    have hRoom := lsh.moveK_hRoom
    rcases applyLadderStep_QPart_moveK lsh hRoom p hp with h | h | h <;>
      subst h <;> simp [kingPos, rookBPos, rookAPos, whiteTopRank]

-- The white *king* specifically is on file 0 (the rook on file 1 is a
-- rook, so it cannot be the piece in question). This is what keeps the
-- kings from being adjacent across the file-2 boundary.
lemma stepBoard_WhiteKingFile0 {n : Nat} {board : Board n} {rank : Fin n}
    {φ : LadderPhase} (lsh : LadderShape board rank φ) :
    ∀ p, (applyLadderStep lsh) p = some ⟨.White, .King⟩ → p.file.val = 0 := by
  intro p hp
  cases φ with
  | moveRb =>
    obtain ⟨_, hRb, _⟩ := applyLadderStep_PiecesAt_moveRb lsh
    rcases applyLadderStep_QPart_moveRb lsh p ⟨.King, hp⟩ with h | h | h
    · subst h; simp [kingPos]
    · subst h; rw [hp] at hRb; simp at hRb
    · subst h; simp [rookAPos]
  | moveRa =>
    obtain ⟨_, hRb, _⟩ := applyLadderStep_PiecesAt_moveRa lsh
    rcases applyLadderStep_QPart_moveRa lsh p ⟨.King, hp⟩ with h | h | h
    · subst h; simp [kingPos]
    · subst h; rw [hp] at hRb; simp at hRb
    · subst h; simp [rookAPos]
  | moveK =>
    have hRoom := lsh.moveK_hRoom
    obtain ⟨_, hRb, _⟩ := applyLadderStep_PiecesAt_moveK lsh hRoom
    rcases applyLadderStep_QPart_moveK lsh hRoom p ⟨.King, hp⟩ with h | h | h
    · subst h; simp [kingPos]
    · subst h; rw [hp] at hRb; simp at hRb
    · subst h; simp [rookAPos]


-- ------------------------------------------------------------
-- CONFINEMENT ⟹ NO CHECK
-- ------------------------------------------------------------
-- Purely local: if every white piece is on file ≤ 1 at rank ≤ m, the
-- white king is on file 0, and the black king is on file ≥ 2 above
-- rank m, then black is not in check. A rook would have to share the
-- king's rank (impossible, it is below m) or file (impossible, it is
-- below 2); the white king is two files away. No line-of-sight
-- reasoning is needed — the attack geometry alone fails.
private lemma noCheck_of_confined {n : Nat} (b : Board n) (m : Nat)
    (hconf : ∀ p, (∃ k, b p = some ⟨.White, k⟩) →
              p.file.val ≤ 1 ∧ p.rank.val ≤ m)
    (hking : ∀ p, b p = some ⟨.White, .King⟩ → p.file.val = 0)
    (hbk : ∀ p, b p = some ⟨.Black, .King⟩ → 2 ≤ p.file.val ∧ m < p.rank.val) :
    ¬ IsCheck b .Black := by
  rintro ⟨kq, hkq, att, hatt⟩
  obtain ⟨hf, hr⟩ := hbk kq hkq
  rcases hatt with ⟨hrook, hvalid⟩ | ⟨hwking, hvalid⟩
  · obtain ⟨hfa, hra⟩ := hconf att ⟨.Rook, hrook⟩
    obtain ⟨-, hdir⟩ := hvalid
    rcases hdir with ⟨heq, -⟩ | ⟨heq, -⟩
    · have := congrArg Fin.val heq; omega
    · have := congrArg Fin.val heq; omega
  · have h0 := hking att hwking
    obtain ⟨-, -, hwf⟩ := hvalid
    unfold WithinOne at hwf
    omega

-- A white piece on the board after the black king steps `src → dst`
-- was already there before: `dst` picks up the black king and `src` is
-- vacated, so any other square is untouched.
private lemma whiteAt_of_moved {n : Nat} (b : Board n) (src dst p : Pos n)
    {k : PieceType} (hsrc : b src = some ⟨.Black, .King⟩)
    (h : (applyMove b src dst) p = some ⟨.White, k⟩) :
    b p = some ⟨.White, k⟩ := by
  rw [applyMove_pieces] at h
  by_cases h1 : p = dst
  · rw [if_pos h1, hsrc] at h; simp at h
  · rw [if_neg h1] at h
    by_cases h2 : p = src
    · rw [if_pos h2] at h; simp at h
    · rw [if_neg h2] at h; exact h


-- ------------------------------------------------------------
-- THE CORE ARGUMENT
-- ------------------------------------------------------------
-- `hroom` is the only phase-dependent input: it says that if the black
-- king sits *on* the ceiling (which happens only in phase moveRa, in
-- check from rookA) then there is a rank above the ceiling to run to.
private lemma black_reply_core {n : Nat} {board : Board n} {rank : Fin n}
    {φ : LadderPhase} (lsh : LadderShape board rank φ) (hn : 3 < n)
    (hroom : ∀ kp : Pos n, (applyLadderStep lsh) kp = some ⟨.Black, .King⟩ →
              kp.rank.val = whiteTopRank rank φ → whiteTopRank rank φ + 1 < n) :
    ∃ src dst : Pos n, IsLegalMove (applyLadderStep lsh) src dst := by
  obtain ⟨hpreRa_le, hle_preRa_succ⟩ := preRa_le_whiteTopRank rank φ lsh.hRfits
  have hlegal' : IsLegalSetup (applyLadderStep lsh) := by
    obtain ⟨-, -, -, -, h⟩ := ladderStep_isLegal lsh; exact h
  obtain ⟨kp, hkp, hkp_uniq⟩ := hlegal'.2.1
  obtain ⟨hkp_file, hkp_rank⟩ := LadderMove_BlackKing_FarFromRa lsh kp hkp
  have hm_le : whiteTopRank rank φ ≤ kp.rank.val := by omega
  have hturn : (applyLadderStep lsh).turn = .Black := by
    obtain ⟨turn_white, -⟩ := lsh.unfold
    show board.turn.opponent = .Black
    rw [turn_white]; rfl
  -- Every square of the safe region other than the king's is empty.
  have hempty : ∀ q : Pos n, 2 ≤ q.file.val → whiteTopRank rank φ < q.rank.val →
      q ≠ kp → (applyLadderStep lsh) q = none := by
    intro q hqf hqr hqne
    rcases hq : (applyLadderStep lsh) q with _ | ⟨c, k⟩
    · rfl
    · exfalso
      cases c with
      | White =>
        obtain ⟨hfile1, -⟩ :=
          LadderMove_OnlyFileOneRaRank_InRegion lsh q (by omega) (by omega) ⟨k, hq⟩
        omega
      | Black =>
        have hk := LadderMove_PreservesOnlyBlackKing lsh q k hq
        subst hk
        exact hqne (hkp_uniq q hq)
  -- ... and safe: relocating the black king there leaves it unattacked.
  have hsafe : ∀ q : Pos n, 2 ≤ q.file.val → whiteTopRank rank φ < q.rank.val →
      q ≠ kp → ¬ IsCheck (applyMove (applyLadderStep lsh) kp q) .Black := by
    intro q hqf hqr hqne
    refine noCheck_of_confined _ (whiteTopRank rank φ) ?_ ?_ ?_
    · rintro p ⟨k, hpk⟩
      exact stepBoard_WhiteConfined lsh p
        ⟨k, whiteAt_of_moved _ kp q p hkp hpk⟩
    · intro p hpk
      exact stepBoard_WhiteKingFile0 lsh p (whiteAt_of_moved _ kp q p hkp hpk)
    · intro p hpk
      rw [applyMove_pieces] at hpk
      by_cases h1 : p = q
      · subst h1; exact ⟨hqf, hqr⟩
      · rw [if_neg h1] at hpk
        by_cases h2 : p = kp
        · rw [if_pos h2] at hpk; simp at hpk
        · rw [if_neg h2] at hpk
          exact absurd (hkp_uniq p hpk) h2
  by_cases hcase : whiteTopRank rank φ < kp.rank.val
  · -- The king is strictly inside the safe rectangle [m+1, n-1] × [2, n-1];
    -- `3 < n` makes it wider than one file, so a neighbour exists.
    have hm1 : whiteTopRank rank φ + 1 < n := by
      have := kp.rank.isLt; omega
    refine IsLegalSetup.king_in_rect_has_legal_move
      (rmin := ⟨whiteTopRank rank φ + 1, hm1⟩) (rmax := ⟨n - 1, by omega⟩)
      (fmin := ⟨2, by omega⟩) (fmax := ⟨n - 1, by omega⟩)
      hlegal' hturn (Or.inr (by show (2 : Nat) < n - 1; omega)) ?_ hkp ?_ ?_
    · refine ⟨?_, ?_, ?_, ?_⟩
      · show whiteTopRank rank φ + 1 ≤ kp.rank.val; omega
      · show kp.rank.val ≤ n - 1; have := kp.rank.isLt; omega
      · show 2 ≤ kp.file.val; omega
      · show kp.file.val ≤ n - 1; have := kp.file.isLt; omega
    · intro q hq hqne
      obtain ⟨hq1, -, hq3, -⟩ := hq
      have hq1' : whiteTopRank rank φ + 1 ≤ q.rank.val := hq1
      exact hempty q hq3 (by omega) hqne
    · intro q hq hqne
      obtain ⟨hq1, -, hq3, -⟩ := hq
      have hq1' : whiteTopRank rank φ + 1 ≤ q.rank.val := hq1
      exact hsafe q hq3 (by omega) hqne
  · -- The king sits on the ceiling (phase moveRa, in check): step up.
    have hkp_eq : kp.rank.val = whiteTopRank rank φ := by omega
    have hm1 : whiteTopRank rank φ + 1 < n := hroom kp hkp hkp_eq
    -- Package the destination abstractly: naming its coordinates keeps
    -- `Fin.val ⟨_, _⟩` out of the arithmetic goals below.
    obtain ⟨q, hq_rank_eq, hq_file_eq⟩ :
        ∃ q : Pos n, q.rank.val = whiteTopRank rank φ + 1 ∧ q.file = kp.file :=
      ⟨⟨⟨whiteTopRank rank φ + 1, hm1⟩, kp.file⟩, rfl, rfl⟩
    have hq_file : 2 ≤ q.file.val := by rw [hq_file_eq]; exact hkp_file
    have hq_rank : whiteTopRank rank φ < q.rank.val := by omega
    have hq_ne : q ≠ kp := by intro heq; rw [heq] at hq_rank_eq; omega
    have hq_empty := hempty q hq_file hq_rank hq_ne
    refine ⟨kp, q, .King, ?_, ?_, ?_, ?_⟩
    · rw [hturn]; exact hkp
    · refine ⟨fun heq => hq_ne heq.symm, ?_, ?_⟩
      · unfold WithinOne; omega
      · rw [hq_file_eq]; unfold WithinOne; omega
    · exact EmptySquare_NotFriendly _ _ hq_empty
    · obtain ⟨hwk, hbk⟩ := NoCaputureMove_PreservesKings _ kp q hlegal' hq_empty
      refine ⟨hwk, hbk, ?_⟩
      have hturn_eq :
          (applyMove (applyLadderStep lsh) kp q).turn.opponent = .Black := by
        show (applyLadderStep lsh).turn.opponent.opponent = .Black
        rw [hturn]; rfl
      rw [hturn_eq]
      exact hsafe q hq_file hq_rank hq_ne


lemma Black_HasLegalReply_NonFinal {n : Nat} (s : LadderState n) (hn : 3 < n)
    (h_not_final : ¬ IsFinalLadderState s) :
    ∃ src dst : Pos n, IsLegalMove (applyLadderStep s.shape) src dst := by
  obtain ⟨board, rank, φ, shape⟩ := s
  refine black_reply_core shape hn ?_
  intro kp hkp hkp_eq
  obtain ⟨-, hkp_rank⟩ := LadderMove_BlackKing_FarFromRa shape kp hkp
  cases φ with
  | moveRb =>
    -- ceiling = pre-move rookA rank, which the black king is strictly above
    exfalso; simp [whiteTopRank, rookAPos] at hkp_eq hkp_rank; omega
  | moveK =>
    exfalso; simp [whiteTopRank, rookAPos] at hkp_eq hkp_rank; omega
  | moveRa =>
    -- non-final: rank + 3 ≠ n, and rank + 2 < n, so rank + 3 < n
    have hne : rank.val + 3 ≠ n := fun h => h_not_final ⟨rfl, h⟩
    have := shape.hRfits
    simp only [whiteTopRank]
    omega

-- Helper: classical-choice extraction of a witness as a (src, dst) pair,
-- which is the type expected by `step` / `hreply` in the termination proof.
noncomputable def blackLegalReply {n : Nat} (s : LadderState n) (hn : 3 < n)
    (h_not_final : ¬ IsFinalLadderState s) : Pos n × Pos n :=
  let ⟨src, hsrc⟩ := Classical.indefiniteDescription _
                       (Black_HasLegalReply_NonFinal s hn h_not_final)
  let ⟨dst, _⟩ := Classical.indefiniteDescription _ hsrc
  (src, dst)

lemma blackLegalReply_isLegal {n : Nat} (s : LadderState n) (hn : 3 < n)
    (h_not_final : ¬ IsFinalLadderState s) :
    IsLegalMove (applyLadderStep s.shape)
      (blackLegalReply s hn h_not_final).1 (blackLegalReply s hn h_not_final).2 :=
  (Classical.indefiniteDescription _
    (Classical.indefiniteDescription _
      (Black_HasLegalReply_NonFinal s hn h_not_final)).2).2
