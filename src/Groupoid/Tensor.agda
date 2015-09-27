{-# OPTIONS --without-K #-}

module Groupoid.Tensor where

open import Agda.Primitive
import Groupoid.Base as G
open import Groupoid.Exponential as Π
import Groupoid.Homotopy as TFor
open import Groupoid.Tensor.Boot public
import Setoid as S
open import Type as T
  using (_,_)

π₀
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (A ⊗ B) Π.⇒₀ᵗ A
π₀ {A = A}{B} = record
  { _$₀_ = T.∐.π₀
  ; -$₁ˢᵐ- = S.∐.π₀
  ; idn = λ { {a , b} →
      S.idnᵗᵐ (G.homˢ A (a , a)) _
    }
  ; cmp = λ { {a}{b}{c} g f →
      S.cmpᵗᵐ (G.homˢ A (T.∐.π₀ a , T.∐.π₀ c))
        ( S.idnᵗᵐ (G.homˢ A (T.∐.π₀ a , T.∐.π₀ c)) _
        , S.idnᵗᵐ (G.homˢ A (T.∐.π₀ a , T.∐.π₀ c)) _ )
    }
  }

π₁
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (A ⊗ B) Π.⇒₀ᵗ B
π₁ {A = A}{B} = record
  { _$₀_ = T.∐.π₁
  ; -$₁ˢᵐ- = S.∐.π₁
  ; idn = λ { {a , b} →
      S.idnᵗᵐ (G.homˢ B (b , b)) _
    }
  ; cmp = λ { {a}{b}{c} g f →
      S.cmpᵗᵐ (G.homˢ B (T.∐.π₁ a , T.∐.π₁ c))
        ( S.idnᵗᵐ (G.homˢ B (T.∐.π₁ a , T.∐.π₁ c)) _
        , S.idnᵗᵐ (G.homˢ B (T.∐.π₁ a , T.∐.π₁ c)) _)
    }
  }
