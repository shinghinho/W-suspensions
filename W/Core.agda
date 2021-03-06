{-# OPTIONS --cubical --safe #-}

module W.Core where

open import Cubical.Foundations.Everything
open import Cubical.Data.Prod
open import Cubical.Data.Sum
open import Cubical.Data.Nat renaming ( zero to β-zero
                                      ; suc to β-suc
                                      )

private
  variable
    i j : Level

data π {i : Level} : Type i where

π-elim : {A : Type i} β π {j} β A
π-elim ()

data π {i : Level} : Type i where
  β : π

data π {i : Level} : Type i where
  ff tt : π

if_then_else_ : {A : Type i} β π {j} β A β A β A
if ff then T else F = F
if tt then T else F = T

data π {i : Level} : Type i where
  ff ft tf tt : π

-- W-suspension
data π² {i : Level}
       (A : Type i)
       (B : A β Type i)
       (C : Type i)
       (l r : C β A) : Type i where
   sup : (a : A) β (B a β π² A B C l r) β π² A B C l r
   cell : (c : C)
        β (t : B (l c) β π² A B C l r)
        β (s : B (r c) β π² A B C l r)
        β sup (l c) t β‘ sup (r c) s

-- Ordinary W-type
W : {i : Level}
  β (A : Type i)
  β (B : A β Type i)
  β Type i
W A B = π² A B π π-elim π-elim

-- W with additional data
Wβ² : {i : Level}
   β (A : Type i)
   β (LP : A β Type i Γ Type i)
   β Type i
Wβ² A LP = W (Ξ£ A (projβ β LP)) (projβ β LP β fst)

βΚ· : Type
βΚ· = W π Ξ» x β if x then π else π

zero : βΚ·
zero = sup ff π-elim

suc : βΚ· β βΚ·
suc n = sup tt Ξ» { β β n }

pattern Zero arg = sup ff arg
pattern Succ arg = sup tt arg

_+βΚ·_ : βΚ· β βΚ· β βΚ·
Zero x +βΚ· b = b
Succ x +βΚ· b = suc (x β +βΚ· b)

one : βΚ·
one = suc zero

two : βΚ·
two = suc one

three : βΚ·
three = suc two

four : βΚ·
four = suc three

five : βΚ·
five = suc four

_ : three +βΚ· two β‘ five
_ = refl

-- List type
ListΚ· : Type β Type
ListΚ· A = Wβ² π Ξ» x β if x then A , π else (π , π)

nil : {A : Type} β ListΚ· A
nil = sup (ff , β) π-elim

cons : {A : Type} β A β ListΚ· A β ListΚ· A
cons x xs = sup (tt , x) Ξ» { β β xs }

pattern [] args = sup (ff , β) args

infixr 2 _β·_
pattern _β·_ x args = sup (tt , x) args

length : {A : Type} β ListΚ· A β βΚ·
length ([] _) = zero
length (x β· xs) = suc (length (xs β))

_ : length (cons zero (cons zero (cons zero (cons zero (cons zero nil))))) β‘ five
_ = refl

βββΚ· : β β βΚ·
βββΚ· β-zero = zero
βββΚ· (β-suc x) = suc (βββΚ· x)

βΚ·ββ : βΚ· β β
βΚ·ββ (Zero _) = β-zero
βΚ·ββ (Succ x) = β-suc (βΚ·ββ (x β))

Isoβ¨β,βΚ·β© : Iso β βΚ·
Iso.fun Isoβ¨β,βΚ·β© = βββΚ·
Iso.inv Isoβ¨β,βΚ·β© = βΚ·ββ
Iso.rightInv Isoβ¨β,βΚ·β© = sec
  where
    sec : section βββΚ· βΚ·ββ
    sec (Zero x) = cong (sup ff) (funExt Ξ» { () })
    sec (Succ x) = cong (sup tt) (funExt Ξ» { β β sec (x β) })
Iso.leftInv Isoβ¨β,βΚ·β© = ret
  where
    ret : retract βββΚ· βΚ·ββ
    ret β-zero = refl
    ret (β-suc a) = cong β-suc (ret a)

ββ‘βΚ· : β β‘ βΚ·
ββ‘βΚ· = isoToPath Isoβ¨β,βΚ·β©

-- Circle as a π²-suspension
π : Type
π = π² π (const π) π (const β) (const β)

base : π
base = sup β π-elim

loop : base β‘ base
loop = cell β π-elim π-elim
