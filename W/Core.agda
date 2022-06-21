{-# OPTIONS --cubical --safe #-}

module W.Core where

open import Cubical.Foundations.Everything
open import Cubical.Data.Prod
open import Cubical.Data.Sum
open import Cubical.Data.Nat renaming ( zero to ℕ-zero
                                      ; suc to ℕ-suc
                                      )

private
  variable
    i j : Level

data 𝟘 {i : Level} : Type i where

𝟘-elim : {A : Type i} → 𝟘 {j} → A
𝟘-elim ()

data 𝟙 {i : Level} : Type i where
  ★ : 𝟙

data 𝟚 {i : Level} : Type i where
  ff tt : 𝟚

if_then_else_ : {A : Type i} → 𝟚 {j} → A → A → A
if ff then T else F = F
if tt then T else F = T

data 𝟜 {i : Level} : Type i where
  ff ft tf tt : 𝟜

-- W-suspension
data 𝒲 {i : Level}
       (A : Type i)
       (B : A → Type i)
       (C : Type i)
       (l r : C → A) : Type i where
   sup : (a : A) → (B a → 𝒲 A B C l r) → 𝒲 A B C l r
   cell : (c : C)
        → (t : B (l c) → 𝒲 A B C l r)
        → (s : B (r c) → 𝒲 A B C l r)
        → sup (l c) t ≡ sup (r c) s

-- Ordinary W-type
W : {i : Level}
  → (A : Type i)
  → (B : A → Type i)
  → Type i
W A B = 𝒲 A B 𝟘 𝟘-elim 𝟘-elim

-- W with additional data
W′ : {i : Level}
   → (A : Type i)
   → (LP : A → Type i × Type i)
   → Type i
W′ A LP = W (Σ A (proj₁ ∘ LP)) (proj₂ ∘ LP ∘ fst)

ℕʷ : Type
ℕʷ = W 𝟚 λ x → if x then 𝟙 else 𝟘

zero : ℕʷ
zero = sup ff 𝟘-elim

suc : ℕʷ → ℕʷ
suc n = sup tt λ { ★ → n }

pattern Zero arg = sup ff arg
pattern Succ arg = sup tt arg

_+ℕʷ_ : ℕʷ → ℕʷ → ℕʷ
Zero x +ℕʷ b = b
Succ x +ℕʷ b = suc (x ★ +ℕʷ b)

one : ℕʷ
one = suc zero

two : ℕʷ
two = suc one

three : ℕʷ
three = suc two

four : ℕʷ
four = suc three

five : ℕʷ
five = suc four

_ : three +ℕʷ two ≡ five
_ = refl

-- List type
Listʷ : Type → Type
Listʷ A = W′ 𝟚 λ x → if x then A , 𝟙 else (𝟙 , 𝟘)

nil : {A : Type} → Listʷ A
nil = sup (ff , ★) 𝟘-elim

cons : {A : Type} → A → Listʷ A → Listʷ A
cons x xs = sup (tt , x) λ { ★ → xs }

pattern [] args = sup (ff , ★) args

infixr 2 _∷_
pattern _∷_ x args = sup (tt , x) args

length : {A : Type} → Listʷ A → ℕʷ
length ([] _) = zero
length (x ∷ xs) = suc (length (xs ★))

_ : length (cons zero (cons zero (cons zero (cons zero (cons zero nil))))) ≡ five
_ = refl

ℕ→ℕʷ : ℕ → ℕʷ
ℕ→ℕʷ ℕ-zero = zero
ℕ→ℕʷ (ℕ-suc x) = suc (ℕ→ℕʷ x)

ℕʷ→ℕ : ℕʷ → ℕ
ℕʷ→ℕ (Zero _) = ℕ-zero
ℕʷ→ℕ (Succ x) = ℕ-suc (ℕʷ→ℕ (x ★))

Iso⟨ℕ,ℕʷ⟩ : Iso ℕ ℕʷ
Iso.fun Iso⟨ℕ,ℕʷ⟩ = ℕ→ℕʷ
Iso.inv Iso⟨ℕ,ℕʷ⟩ = ℕʷ→ℕ
Iso.rightInv Iso⟨ℕ,ℕʷ⟩ = sec
  where
    sec : section ℕ→ℕʷ ℕʷ→ℕ
    sec (Zero x) = cong (sup ff) (funExt λ { () })
    sec (Succ x) = cong (sup tt) (funExt λ { ★ → sec (x ★) })
Iso.leftInv Iso⟨ℕ,ℕʷ⟩ = ret
  where
    ret : retract ℕ→ℕʷ ℕʷ→ℕ
    ret ℕ-zero = refl
    ret (ℕ-suc a) = cong ℕ-suc (ret a)

ℕ≡ℕʷ : ℕ ≡ ℕʷ
ℕ≡ℕʷ = isoToPath Iso⟨ℕ,ℕʷ⟩

-- Circle as a 𝒲-suspension
𝕊 : Type
𝕊 = 𝒲 𝟙 (const 𝟘) 𝟙 (const ★) (const ★)

base : 𝕊
base = sup ★ 𝟘-elim

loop : base ≡ base
loop = cell ★ 𝟘-elim 𝟘-elim
