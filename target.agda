module target where

-- Operator precedence and associativity
infix 4 _≤ₙ_ _<ₙ_ _≤ₛ_
infixl 6 _+ₙ_ _∸ₙ_ _+ₛ_ _∸ₛ_ _-ₛ_
infixl 7 _*ₙ_

open import Data.Integer hiding (suc)

-- Natural numbers
data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ
-- {-# BUILTIN NATURAL ℕ #-}

-- data ℤ : Set where
--     pos : ℕ → ℤ
--     negsuc : ℕ → ℤ
-- {-# BUILTIN INTEGER       ℤ    #-}
-- {-# BUILTIN INTEGERPOS    pos    #-}
-- {-# BUILTIN INTEGERNEGSUC negsuc #-}

_+ₙ_ : ℕ → ℕ → ℕ
zero +ₙ n = n
suc m +ₙ n = suc (m +ₙ n)
-- {-# BUILTIN NATPLUS _+ₙ_ #-}

-- Monus (a∸b = max{a-b, 0})
_∸ₙ_ : ℕ → ℕ → ℕ
m ∸ₙ zero = m
zero ∸ₙ suc n = zero
suc m ∸ₙ suc n = m ∸ₙ n
-- {-# BUILTIN NATMINUS _∸ₙ_ #-}

_*ₙ_ : ℕ → ℕ → ℕ
zero *ₙ n = zero
suc m *ₙ n = n +ₙ m *ₙ n
-- {-# BUILTIN NATTIMES _*ₙ_ #-}

-- Relations of natural numbers
data _≤ₙ_ : ℕ → ℕ → Set where
    z≤ₙn : ∀ {n : ℕ} → zero ≤ₙ n
    s≤ₙs : ∀ {m n : ℕ} → m ≤ₙ n → suc m ≤ₙ suc n

-- inv-s≤s : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
-- inv-s≤s (s≤s m≤n) = m≤n

≤ₙ-refl : ∀ {n : ℕ} → n ≤ₙ n
≤ₙ-refl {zero} = z≤ₙn
≤ₙ-refl {suc n} = s≤ₙs ≤ₙ-refl

≤ₙ-trans : ∀ {m n p : ℕ} → m ≤ₙ n → n ≤ₙ p → m ≤ₙ p
≤ₙ-trans z≤ₙn _ = z≤ₙn
≤ₙ-trans (s≤ₙs m≤ₙn) (s≤ₙs n≤ₙp) = s≤ₙs (≤ₙ-trans m≤ₙn n≤ₙp)

data _<ₙ_ : ℕ → ℕ → Set where
    z<ₙs : ∀ {n : ℕ} → zero <ₙ suc n
    s<ₙs : ∀ {m n : ℕ} → m <ₙ n → suc m <ₙ suc n

<ₙ→≤ₙ : ∀ {m n : ℕ} → m <ₙ n → suc m ≤ₙ n
<ₙ→≤ₙ (z<ₙs) = s≤ₙs z≤ₙn
<ₙ→≤ₙ (s<ₙs m<ₙn) = s≤ₙs (<ₙ→≤ₙ m<ₙn)

data Fin : ℕ → Set where
  fzero : ∀{n} → Fin (suc n)
  fsuc : ∀{n} → (i : Fin n) → Fin (suc n)

toℕ : ∀ {m} → Fin m → ℕ
toℕ fzero = zero
toℕ (fsuc i) = suc (toℕ i)

-- Minus
-- _-_ : (m : ℕ) → (n : ℕ) → (n ≤ m) → ℕ
-- (m - n) _ = m ∸ n
-- (m - zero) _ = m
-- (suc m - suc n) p = (m - n) (inv-s≤s p)
_-ₙ_ : (m : ℕ) → (n : Fin m) → ℕ
m -ₙ n = m ∸ₙ toℕ n

-- Stack descriptor: (frames, displacement)
record SD : Set where
    constructor ⟨_,_⟩
    field
        f : ℕ
        d : ℕ

-- Stack descriptor operations    
_+ₛ_ : SD → ℕ → SD
⟨ S_f , S_d ⟩ +ₛ n = ⟨ S_f , S_d +ₙ n ⟩

_∸ₛ_ : SD → ℕ → SD
⟨ S_f , S_d ⟩ ∸ₛ n = ⟨ S_f , S_d ∸ₙ n ⟩

-- _-ₛ_ : (sd : SD) → (n : ℕ) → n ≤ SD.d sd → SD
-- (⟨ S_f , S_d ⟩ -ₛ n) p = ⟨ S_f , (S_d - n) p ⟩

_-ₛ_ : (sd : SD) → Fin (SD.d sd) → SD
⟨ S_f , S_d ⟩ -ₛ n = ⟨ S_f , S_d -ₙ n ⟩

-- Stack descriptor lexicographic ordering
data _≤ₛ_ : SD → SD → Set where
    <ₙ-f : ∀ {S_f S'_f S_d S'_d} → S_f <ₙ S'_f → ⟨ S_f , S_d ⟩ ≤ₛ ⟨ S'_f , S'_d ⟩
    ≤ₙ-d : ∀ {S_f S_d S'_d} → S_d ≤ₙ S'_d → ⟨ S_f , S_d ⟩ ≤ₛ ⟨ S_f , S'_d ⟩

-- Operator
data UnaryOp : Set where 
    UNeg : UnaryOp

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
    l-var : (sdᵛ : SD) → sdᵛ ≤ₛ sd ∸ₛ suc (zero) → L sd
    l-sbrs : L sd

-- Simple righthand sides
data S (sd : SD) : Set where
    s-l : L sd → S sd
    s-lit : ℤ → S sd

-- Righthand sides
data R (sd : SD) : Set where
    r-s : S sd → R sd
    r-unary : UnaryOp → S sd → R sd
    r-binary : S sd → BinaryOp → S sd → R sd

-- Instruction sequences
data I (sd : SD) : Set where
    stop : I sd
    assign_inc : (δ : ℕ) → L (sd +ₛ δ) → R sd → I (sd +ₛ δ) → I sd
    assign_dec : (δ : Fin (SD.d sd)) → L (sd -ₛ δ) → R sd → I (sd -ₛ δ)  → I sd
    if-then-else_inc : (δ : ℕ) → S sd → RelOp → S sd → I (sd +ₛ δ) → I (sd +ₛ δ) → I sd
    if-then-else_dec : (δ : Fin (SD.d sd)) → S sd → RelOp → S sd → I (sd -ₛ δ) → I (sd -ₛ δ) → I sd
    adjustdisp_inc : (δ : ℕ) → I (sd +ₛ δ) → I sd
    adjustdisp_dec : (δ : Fin (SD.d sd)) → I (sd -ₛ δ) → I sd
    popto : (sd' : SD) → sd' ≤ₛ sd → I sd' → I sd