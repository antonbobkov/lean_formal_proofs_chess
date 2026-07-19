import ChessRules
import TRC_FunctionWithInvariant
import LadderStepIsLegal
import TRC_Invariant_BlackEmpty
import TRC_Invariant_CheckLocations

-- ============================================================
-- FINAL LADDER STATE
-- ============================================================
-- A "final" ladder state is the unique configuration from which White's
-- next ply checkmates Black. In our system this is phase = moveRa with
-- rank.val + 3 = n (so rookA after applyLadderStep sits at (n-1, 0),
-- pinning the Black king on rank n-1 with no escape).

def IsFinalLadderState {n : Nat} (s : LadderState n) : Prop :=
  s.phase = .moveRa ∧ s.rank.val + 3 = n

instance {n : Nat} (s : LadderState n) : Decidable (IsFinalLadderState s) := by
  unfold IsFinalLadderState; infer_instance

-- After applyLadderStep on a final state, the Black king is in check
-- from rookA, which has just moved to (rank+2, 0) = (n-1, 0). The Black
-- king is forced to rank n-1 by the LadderShape invariants
-- (rank > rookAPos.rank = rank+1 plus rank < n; with rank+3 = n the
-- only legal Black-king rank is n-1).
lemma LadderStep_IsCheck_AtFinal {n : Nat} (s : LadderState n)
    (h_final : IsFinalLadderState s) :
    IsCheck (applyLadderStep s.shape) .Black := by
  obtain ⟨board, rank, phase, shape⟩ := s
  obtain ⟨h_phase, h_rank⟩ := h_final
  subst h_phase
  -- The step board is a legal setup, so it has a (unique) black king.
  obtain ⟨_, _, _, _, h_step_legal⟩ := ladderStep_isLegal shape
  obtain ⟨_, ⟨kp, hkp, _⟩, _⟩ := h_step_legal
  -- That king has file ≥ 2 and rank strictly above the pre-move rookA
  -- rank (= rank + 1). With rank + 3 = n and kp.rank < n, its rank is
  -- pinned to rank + 2 — exactly one above the pre-move rookA.
  obtain ⟨hfile, hrank⟩ := LadderMove_BlackKing_FarFromRa shape kp hkp
  refine LadderMove_BlackInCheck_AtRaRankPlusOne_FileGe2_moveRa
    shape kp hkp ?_ hfile
  have hRa : (rookAPos rank .moveRa shape.hRfits).rank.val = rank.val + 1 := rfl
  have hn : rank.val + 3 = n := h_rank
  have hlt := kp.rank.isLt
  omega

-- Membership in `kingMoveTargets` carries the geometric condition.
private lemma validKingMove_of_mem_targets {n : Nat} (b : Board n)
    (src dst : Pos n) (c : Color) (h : dst ∈ kingMoveTargets b src c) :
    ValidKingMove src dst := by
  unfold kingMoveTargets at h
  rw [List.mem_filter] at h
  rw [Bool.and_eq_true] at h
  exact of_decide_eq_true h.2.1

-- After a black king move src → dst, the black king is unique at dst:
-- `dst` picks it up, `src` is vacated, and any other square carrying it
-- would have carried it before the move too.
private lemma blackKing_unique_after_move {n : Nat} (b : Board n)
    (src dst : Pos n) (huniq : ∀ p, b p = some ⟨.Black, .King⟩ → p = src) :
    ∀ p, (applyMove b src dst) p = some ⟨.Black, .King⟩ → p = dst := by
  intro p hp
  rw [applyMove_pieces] at hp
  by_cases h1 : p = dst
  · exact h1
  · rw [if_neg h1] at hp
    by_cases h2 : p = src
    · rw [if_pos h2] at hp; simp at hp
    · rw [if_neg h2] at hp
      exact absurd (huniq p hp) h2

-- After applyLadderStep on a final state, the Black king has no legal
-- destination. With rank + 3 = n the Black king is pinned to rank n-1
-- (= rank+2) at file ≥ 2, so a king step lands on rank rank+1 or rank+2
-- at file ≥ 1, and each such square is covered:
--   • rank+2 (any file ≥ 1) — rookA, from (rank+2, 0) along the rank;
--   • rank+1, file ≥ 2      — rookB, from (rank+1, 1) along the rank;
--   • rank+1, file = 1      — capturing rookB, but that square is
--     diagonally adjacent to the White king at (rank, 0).
-- Stated in the form the second conjunct of IsCheckmate uses.
lemma LadderStep_NoKingEscape_AtFinal {n : Nat} (s : LadderState n)
    (h_final : IsFinalLadderState s) :
    ∀ src,
      (applyLadderStep s.shape) src = some ⟨.Black, .King⟩ →
      ∀ dst ∈ kingMoveTargets (applyLadderStep s.shape) src .Black,
        IsCheck (applyMove (applyLadderStep s.shape) src dst) .Black := by
  obtain ⟨board, rank, phase, shape⟩ := s
  obtain ⟨h_phase, h_rank⟩ := h_final
  subst h_phase
  have hn : rank.val + 3 = n := h_rank
  intro src hsrc dst hdst
  -- White's three squares after the ply: (rank,0), (rank+1,1), (rank+2,0).
  obtain ⟨hK, hRb, hRa⟩ := applyLadderStep_PiecesAt_moveRa shape
  have hK_rank : (kingPos rank shape.hRfits).rank.val = rank.val := rfl
  have hK_file : (kingPos rank shape.hRfits).file.val = 0 := rfl
  have hRb_rank : (rookBPos rank .moveK shape.hRfits).rank.val = rank.val + 1 := rfl
  have hRb_file : (rookBPos rank .moveK shape.hRfits).file.val = 1 := rfl
  have hRa_rank : (rookAPos rank .moveK shape.hRfits).rank.val = rank.val + 2 := rfl
  have hRa_file : (rookAPos rank .moveK shape.hRfits).file.val = 0 := rfl
  have hpreRa : (rookAPos rank .moveRa shape.hRfits).rank.val = rank.val + 1 := rfl
  -- The Black king is pinned to rank+2, at file >= 2.
  obtain ⟨hsrc_file, hsrc_rank⟩ := LadderMove_BlackKing_FarFromRa shape src hsrc
  have hsrc_lt := src.rank.isLt
  have hsrc_eq : src.rank.val = rank.val + 2 := by omega
  have hlegal' : IsLegalSetup (applyLadderStep shape) := by
    obtain ⟨-, -, -, -, h⟩ := ladderStep_isLegal shape; exact h
  obtain ⟨bk, -, hbk_uniq⟩ := hlegal'.2.1
  have huniq' : ∀ p, (applyLadderStep shape) p = some ⟨.Black, .King⟩ → p = src :=
    fun p hp => (hbk_uniq p hp).trans (hbk_uniq src hsrc).symm
  -- Destination bounds from the king step.
  obtain ⟨hne, hwr, hwf⟩ := validKingMove_of_mem_targets _ _ _ _ hdst
  have hdst_lt := dst.rank.isLt
  unfold WithinOne at hwr hwf
  have hdst_rank : dst.rank.val = rank.val + 1 ∨ dst.rank.val = rank.val + 2 := by omega
  have hdst_file : 1 ≤ dst.file.val := by omega
  -- Squares with file >= 1 above rank+1, other than rookB's, are empty.
  have hempty : ∀ q : Pos n, 1 ≤ q.file.val → rank.val + 1 ≤ q.rank.val →
      ¬ (q.file.val = 1 ∧ q.rank.val = rank.val + 1) → q ≠ src →
      (applyLadderStep shape) q = none := by
    intro q hf hr hnot hqne
    rcases hq : (applyLadderStep shape) q with _ | ⟨c, k⟩
    · rfl
    · exfalso
      cases c with
      | White =>
        obtain ⟨h1, h2⟩ :=
          LadderMove_OnlyFileOneRaRank_InRegion shape q hf (by omega) ⟨k, hq⟩
        exact hnot ⟨h1, by omega⟩
      | Black =>
        have hk := LadderMove_PreservesOnlyBlackKing shape q k hq
        subst hk
        exact hqne (huniq' q hq)
  -- Post-move bookkeeping shared by all three cases.
  have hb_dst : (applyMove (applyLadderStep shape) src dst) dst
      = some ⟨.Black, .King⟩ := by rw [applyMove_pieces, if_pos rfl]; exact hsrc
  have honly_bk := applyMove_PreservesOnlyBlackKing (applyLadderStep shape) src dst
    (LadderMove_PreservesOnlyBlackKing shape)
  have huniq_dst := blackKing_unique_after_move (applyLadderStep shape) src dst huniq'
  -- A white piece surviving the black reply was already white before it.
  have hwhite_before : ∀ p k,
      (applyMove (applyLadderStep shape) src dst) p = some ⟨.White, k⟩ →
      (applyLadderStep shape) p = some ⟨.White, k⟩ := by
    intro p k hpk
    rw [applyMove_pieces] at hpk
    by_cases h1 : p = dst
    · rw [if_pos h1, hsrc] at hpk; simp at hpk
    · rw [if_neg h1] at hpk
      by_cases h2 : p = src
      · rw [if_pos h2] at hpk; simp at hpk
      · rw [if_neg h2] at hpk; exact hpk
  rcases hdst_rank with hdr | hdr
  · -- dst on rank+1
    by_cases hdf : dst.file.val = 1
    · -- capturing rookB, but the White king covers (rank+1, 1) diagonally
      have hK_ne_dst : kingPos rank shape.hRfits ≠ dst := by
        intro heq; rw [heq] at hK_rank; omega
      have hK_ne_src : kingPos rank shape.hRfits ≠ src := by
        intro heq; rw [heq] at hK_rank; omega
      have hK' : (applyMove (applyLadderStep shape) src dst)
          (kingPos rank shape.hRfits) = some ⟨.White, .King⟩ := by
        rw [applyMove_pieces, if_neg hK_ne_dst, if_neg hK_ne_src]; exact hK
      exact ⟨dst, hb_dst, kingPos rank shape.hRfits,
        .inr ⟨hK', hK_ne_dst, by unfold WithinOne; omega,
              by unfold WithinOne; omega⟩⟩
    · -- rookB attacks along rank+1
      have hdst_empty := hempty dst hdst_file (by omega) (by omega) (fun h => hne h.symm)
      refine RookCheckRight _ (rookBPos rank .moveK shape.hRfits) dst ?_ hb_dst
        honly_bk huniq_dst ?_ ?_ ?_
      · refine NoCaptureMove_PreservesPiece _ _ _ _ _ hRb ?_ hdst_empty
        intro heq; rw [← heq] at hRb_rank; omega
      · intro p k hp_rank hp_file hpk
        have hpk' := hwhite_before p k hpk
        have hp_rank' : p.rank.val = rank.val + 1 := by rw [hp_rank]; omega
        rcases applyLadderStep_QPart_moveRa shape p ⟨k, hpk'⟩ with h | h | h <;>
          subst h <;> omega
      · apply Fin.ext; omega
      · omega
  · -- dst on rank+2: rookA attacks along its own rank
    have hdst_empty := hempty dst hdst_file (by omega) (by omega) (fun h => hne h.symm)
    refine RookCheckRight _ (rookAPos rank .moveK shape.hRfits) dst ?_ hb_dst
      honly_bk huniq_dst ?_ ?_ ?_
    · refine NoCaptureMove_PreservesPiece _ _ _ _ _ hRa ?_ hdst_empty
      -- src shares rookA's rank, so separate them by file instead
      intro heq; rw [← heq] at hRa_file; omega
    · intro p k hp_rank hp_file hpk
      have hpk' := hwhite_before p k hpk
      have hp_rank' : p.rank.val = rank.val + 2 := by rw [hp_rank]; omega
      rcases applyLadderStep_QPart_moveRa shape p ⟨k, hpk'⟩ with h | h | h <;>
        subst h <;> omega
    · apply Fin.ext; omega
    · omega

-- Black has no rook (LadderShape's only-Black-King clause), so the
-- rook part of IsCheckmate is vacuous.
lemma LadderStep_NoBlackRook {n : Nat} (s : LadderState n) :
    ∀ src, (applyLadderStep s.shape) src ≠ some ⟨.Black, .Rook⟩ := by
  intro src h_rook
  exact PieceType.noConfusion
    (LadderMove_PreservesOnlyBlackKing s.shape src .Rook h_rook)

-- Combining the three: applyLadderStep on a final state delivers checkmate.
theorem IsCheckmate_AtFinal {n : Nat} (s : LadderState n)
    (h_final : IsFinalLadderState s) :
    IsCheckmate (applyLadderStep s.shape) .Black := by
  refine ⟨LadderStep_IsCheck_AtFinal s h_final, fun src => ⟨?_, ?_⟩⟩
  · exact LadderStep_NoKingEscape_AtFinal s h_final src
  · intro h_rook
    exact absurd h_rook (LadderStep_NoBlackRook s src)
