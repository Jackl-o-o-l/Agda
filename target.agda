-- Operator precedence and associativity
infix 4 _≤_ _<_ _≤ₛ_
infixl 6 _+_ _∸_ _+ₛ_ _∸ₛ_
infixl 7 _*_

-- Natural numbers
data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

-- Monus (a∸b = max{a-b, 0})
_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n

_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + m * n

-- Relations of natural numbers
data _≤_ : ℕ → ℕ → Set where
    z≤n : ∀ {n : ℕ} → zero ≤ n
    s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

data _<_ : ℕ → ℕ → Set where
    z<s : ∀ {n : ℕ} → zero < suc n
    s<s : ∀ {m n : ℕ} → m < n → suc m < suc n

<→≤ : ∀ {m n : ℕ} → m < n → suc m ≤ n
<→≤ (z<s) = s≤s z≤n
<→≤ (s<s m<n) = s≤s (<→≤ m<n)

-- Stack descriptor: (frames, displacement)
record SD : Set where
    constructor ⟨_,_⟩
    field
        f : ℕ
        d : ℕ

-- Stack descriptor operations    
_+ₛ_ : SD → ℕ → SD
⟨ S_f , S_d ⟩ +ₛ n = ⟨ S_f , S_d + n ⟩

_∸ₛ_ : SD → ℕ → SD
⟨ S_f , S_d ⟩ ∸ₛ n = ⟨ S_f , S_d ∸ n ⟩

-- Stack descriptor lexicographic ordering
data _≤ₛ_ : SD → SD → Set where
    <-f : ∀ {S_f S'_f S_d S'_d} → S_f < S'_f → ⟨ S_f , S_d ⟩ ≤ₛ ⟨ S'_f , S'_d ⟩
    ≤-d : ∀ {S_f S_d S'_d} → S_d ≤ S'_d → ⟨ S_f , S_d ⟩ ≤ₛ ⟨ S_f , S'_d ⟩

-- Operator
data UnaryOp : Set where 
    UMinus : UnaryOp

data BinaryOp : Set where
    BPlus : BinaryOp
    BMinus : BinaryOp
    BTimes : BinaryOp

data RelOp : Set where
    RLeq : RelOp
    RLt : RelOp

-- Nonterminals
-- Lefthand sides
data L (sd : SD) : Set where
    l-var : (sdᵛ : SD) → sdᵛ ≤ₛ sd ∸ₛ suc zero → L sd
    l-sbrs : L sd

-- Simple righthand sides
data S (sd : SD) : Set where
    s-l : L sd → S sd
    s-lit : ℕ → S sd

-- Righthand sides
data R (sd : SD) : Set where
    r-s : S sd → R sd
    r-unary : UnaryOp → S sd → R sd
    r-binary : S sd → BinaryOp → S sd → R sd