infixl 6 _+_ _∸_
infixl 7 _*_

data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n

_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + m * n