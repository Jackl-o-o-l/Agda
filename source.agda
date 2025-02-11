module source where

-- Operator precedence and associativity
infix 1 _≤:_
infix 2 _⟶_ 
infix 4 _⊢_
infix 4 _∈_
infixl 5 _,_
infixr 7 _⇒_

-- Types
data Type : Set where
    comm : Type
    intexp : Type
    intacc : Type
    intvar : Type
    ℕ : Type
    ℤ : Type
    _⇒_ : Type  →  Type  →  Type

-- Contexts
data Context : Set where
    · : Context
    _,_ : Context  →  Type  →  Context

-- Variables and the lookup judgement
data _∈_ : Type  →  Context  →  Set where
    Z : ∀{Γ A}  →  A ∈ Γ , A
    S : ∀{Γ A B}  →  B ∈ Γ  →  B ∈ Γ , A

-- Terms and the typing judgement
data _⊢_ : Context  →  Type  →  Set where
    Var : ∀{Γ A}  →  A ∈ Γ  →  Γ ⊢ A

    -- lambda function and application
    Lambda : ∀{Γ A B}  →  Γ , A ⊢ B  →  Γ ⊢ A ⇒ B
    App : ∀{Γ A B}  →  Γ ⊢ A ⇒ B  →  Γ ⊢ A  →  Γ ⊢ B

    -- constants
    Zero : ∀{Γ}  →  Γ ⊢ ℕ
    Suc : ∀{Γ}  →  Γ ⊢ ℕ  →  Γ ⊢ ℕ
    Pos : ∀{Γ}  →  Γ ⊢ ℕ  →  Γ ⊢ ℤ
    Negsuc : ∀{Γ}  →  Γ ⊢ ℕ  →  Γ ⊢ ℤ

    -- command
    Seq : ∀{Γ} → Γ ⊢ comm → Γ ⊢ comm → Γ ⊢ comm

    -- intexp
    Neg : ∀{Γ} → Γ ⊢ intexp → Γ ⊢ intexp
    Plus : ∀{Γ} → Γ ⊢ intexp → Γ ⊢ intexp → Γ ⊢ intexp


data Value : ∀{Γ A}  →  Γ ⊢ A  →  Set where
    V-Zero : ∀{Γ}  →  Value (Zero {Γ})
    V-Suc : ∀{Γ} {V : Γ ⊢ ℕ}  →  Value V  →  Value (Suc V)
    V-Pos : ∀{Γ} {V : Γ ⊢ ℕ}  →  Value V  →  Value (Pos V) 
    V-Negsuc : ∀{Γ} {V : Γ ⊢ ℕ}  →  Value V  →  Value (Pos V) 

    V-Lambda : ∀{Γ A B} {F : Γ , A ⊢ B}  →  Value (Lambda F)

-- Renaming
ext : ∀{Γ Δ}  →  (∀{A}  →  A ∈ Γ  →  A ∈ Δ)  →  (∀{A B}  →  B ∈ Γ , A  →  B ∈ Δ , A)
ext ρ Z = Z
ext ρ (S x) = S (ρ x)

rename : ∀{Γ Δ}  →  (∀{A}  →  A ∈ Γ  →  A ∈ Δ)  →  (∀{A}  →  Γ ⊢ A  →  Δ ⊢ A)
rename ρ (Var x) = Var (ρ x)
rename ρ (Lambda F) = Lambda (rename (ext ρ) F)
rename ρ (App F E) = App (rename ρ F) (rename ρ E)
rename ρ Zero = Zero
rename ρ (Suc N) = Suc (rename ρ N)
rename ρ (Pos N) = Pos (rename ρ N)
rename ρ (Negsuc N) = Negsuc (rename ρ N)
rename ρ (Seq c₁ c₂) = Seq (rename ρ c₁) (rename ρ c₂)
rename ρ (Neg I) = Neg (rename ρ I)
rename ρ (Plus I₁ I₂) = Plus (rename ρ I₁) (rename ρ I₂)

-- Simultaneous substitution
exts : ∀{Γ Δ}  →  (∀{A}  →  A ∈ Γ  →  Δ ⊢ A)  →  (∀{A B}  →  B ∈ Γ , A  →  Δ , A ⊢ B)
exts σ Z = Var Z
exts σ (S x) = rename S (σ x)

subst : ∀{Γ Δ}  →  (∀{A}  →  A ∈ Γ  →  Δ ⊢ A)  →  (∀{A}  →  Γ ⊢ A  →  Δ ⊢ A)
subst σ (Var x) = σ x
subst σ (Lambda F) = Lambda (subst (exts σ) F)
subst σ (App F E) = App (subst σ F) (subst σ E)
subst σ Zero = Zero
subst σ (Suc N) = Suc (subst σ N)
subst σ (Pos N) = Pos (subst σ N)
subst σ (Negsuc N) = Negsuc (subst σ N)
subst σ (Seq c₁ c₂) = Seq (subst σ c₁) (subst σ c₂)
subst σ (Neg I) = Neg (subst σ I)
subst σ (Plus I₁ I₂) = Plus (subst σ I₁) (subst σ I₂)

-- Single substitution
_[_] : ∀{Γ A B}  →  Γ , B ⊢ A  →  Γ ⊢ B → Γ ⊢ A
_[_] {Γ} {A} {B} N M = subst {Γ , B} {Γ} σ {A} N
    where
    σ : ∀ {A}  →  A ∈ Γ , B  →  Γ ⊢ A
    σ Z = M
    σ (S x) = Var x

-- Reduction
data _⟶_ : ∀{Γ A}  →  (Γ ⊢ A)  →  (Γ ⊢ A)  →  Set where
    Suc-cong : ∀{Γ} {N N′ : Γ ⊢ ℕ}  →  N ⟶ N′  →  Suc N ⟶ Suc N′
    Pos-cong : ∀{Γ} {N N′ : Γ ⊢ ℕ}  →  N ⟶ N′  →  Pos N ⟶ Pos N′
    Negsuc-cong : ∀{Γ} {N N′ : Γ ⊢ ℕ}  →  N ⟶ N′  →  Negsuc N ⟶ Negsuc N′
    
    App-cong₁ : ∀{Γ A B} {F F′ : Γ ⊢ A ⇒ B} {E : Γ ⊢ A}  →  F ⟶ F′  →  App F E ⟶ App F′ E
    App-cong₂ : ∀{Γ A B} {V : Γ ⊢ A ⇒ B} {E E′ : Γ ⊢ A}  →  Value V  →  E ⟶ E′  →  App V E ⟶ App V E′
    Lambda-β : ∀{Γ A B} {F : Γ , A ⊢ B} {V : Γ ⊢ A}  →  Value V  →  App (Lambda F) V ⟶ F [ V ]

-- Subtype relation
data _≤:_ : Type  →  Type  →  Set where
    ≤:-refl : ∀{T}  →  T ≤: T
    ≤:-trans : ∀{T T′ T″}  →  T ≤: T′  →  T′ ≤: T″  →  T ≤: T″
    ≤:-fn : ∀{T₁ T₁′ T₂ T₂′}  →  T₁′ ≤: T₁  →  T₂ ≤: T₂′  →  T₁ ⇒ T₂ ≤: T₁′ ⇒ T₂′

    var-≤:-exp : intvar ≤: intexp
    var-≤:-acc : intvar ≤: intacc
    ℕ-≤:-ℤ : ℕ ≤: ℤ