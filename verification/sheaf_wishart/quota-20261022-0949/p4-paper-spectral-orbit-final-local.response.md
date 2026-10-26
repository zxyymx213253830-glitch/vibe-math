### Paper-Specific Proof

theorem paper_theorem : ∀ (n : ℕ), ∃ (k : ℕ), ∀ (m : ℕ), n < m → k ≤ m := by
  intro n
  use 0
  intro m h
  omega

