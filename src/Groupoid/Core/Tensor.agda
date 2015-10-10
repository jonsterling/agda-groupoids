{-# OPTIONS --without-K #-}

module Groupoid.Core.Tensor where

open import Agda.Primitive
import Groupoid.Core.Base as G
open import Groupoid.Core.Hom as Π
import Groupoid.Core.Homotopy as TF
open import Groupoid.Core.Tensor.Boot public
import Setoid as S
open import Type as T
  using (_,_)

π₀
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (A ⊗ B) Π.⇒₀ᵗ A
_$₀_ π₀ =
  T.∐.π₀
-$₁ˢ- π₀ =
  S.∐.π₀
idn (π₀ {A = A}) =
  λ {a} → S.idnᵗ (G.homˢ A (T.∐.π₀ a , T.∐.π₀ a)) _
cmp (π₀ {A = A}) =
  λ {a}{_}{c} _ _ → S.idnᵗ (G.homˢ A (T.∐.π₀ a , T.∐.π₀ c)) _

π₁
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (A ⊗ B) Π.⇒₀ᵗ B
_$₀_ π₁ =
  T.∐.π₁
-$₁ˢ- π₁ =
  S.∐.π₁
idn (π₁ {B = B}) =
  λ {a} → S.idnᵗ (G.homˢ B (T.∐.π₁ a , T.∐.π₁ a)) _
cmp (π₁ {B = B}) =
  λ {a}{_}{c} _ _ → S.idnᵗ (G.homˢ B (T.∐.π₁ a , T.∐.π₁ c)) _

⟨-,-⟩
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {X : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {A : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {B : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → ((X Π.⇒₀ᵍ A) ⊗ (X Π.⇒₀ᵍ B)) Π.⇒₀ᵗ (X Π.⇒₀ᵍ A ⊗ B)
_$₀_ (_$₀_ ⟨-,-⟩ FG) =
  T.∐.⟨ T.∐.π₀ FG $₀_ , T.∐.π₁ FG $₀_ ⟩
-$₁ˢ- (_$₀_ ⟨-,-⟩ FG) =
  S.∐.⟨-,-⟩ S.Π.$₀ (-$₁ˢ- (T.∐.π₀ FG) , -$₁ˢ- (T.∐.π₁ FG))
idn (_$₀_ ⟨-,-⟩ (F , G)) =
  Π.idn F , Π.idn G
cmp (_$₀_ ⟨-,-⟩ (F , G)) _ _ =
  cmp F _ _ , cmp G _ _
TF.com₁ (S.Π._$₀_ (-$₁ˢ- ⟨-,-⟩) (α , β)) =
  TF.com₁ α , TF.com₁ β
TF.nat₁ (S.Π._$₀_ (-$₁ˢ- ⟨-,-⟩) (α , β)) _ =
  TF.nat₁ α _ , TF.nat₁ β _
TF.com₂ (S.Π._$₁_ (-$₁ˢ- ⟨-,-⟩) (α¹ , β¹)) =
  TF.com₂ α¹ , TF.com₂ β¹
TF.com₂ (idn (⟨-,-⟩ {A = A}{B})) =
  S.idnᵗ (G.homˢ A _) _ , S.idnᵗ (G.homˢ B _) _
TF.com₂ (cmp (⟨-,-⟩ {A = A}{B}) _ _) =
  S.idnᵗ (G.homˢ A _) _ , S.idnᵗ (G.homˢ B _) _

⟨-⊗-⟩
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ ℓ₃ᵒ ℓ₃ˢᵒ ℓ₃ˢʰ}
  → {X₀ : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {X₁ : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {B : G.t d ℓ₃ᵒ ℓ₃ˢᵒ ℓ₃ˢʰ}
  → ((X₀ Π.⇒₀ᵍ A) ⊗ (X₁ Π.⇒₀ᵍ B)) Π.⇒₀ᵗ ((X₀ ⊗ X₁) Π.⇒₀ᵍ (A ⊗ B))
_$₀_ (_$₀_ ⟨-⊗-⟩ FG) =
  T.∐.⟨ T.∐.π₀ FG $₀_ ⊗ T.∐.π₁ FG $₀_ ⟩
-$₁ˢ- (_$₀_ ⟨-⊗-⟩ FG) =
  S.∐.⟨-⊗-⟩ S.Π.$₀ (-$₁ˢ- (T.∐.π₀ FG) , -$₁ˢ- (T.∐.π₁ FG))
idn (_$₀_ ⟨-⊗-⟩ (F , G)) =
  Π.idn F , Π.idn G
cmp (_$₀_ ⟨-⊗-⟩ (F , G)) _ _ =
  Π.cmp F _ _ , Π.cmp G _ _
TF.com₁ (S.Π._$₀_ (-$₁ˢ- ⟨-⊗-⟩) (α , β)) =
  TF.com₁ α , TF.com₁ β
TF.nat₁ (S.Π._$₀_ (-$₁ˢ- ⟨-⊗-⟩) (α , β)) _ =
  TF.nat₁ α _ , TF.nat₁ β _
TF.com₂ (S.Π._$₁_ (-$₁ˢ- ⟨-⊗-⟩) (α¹ , β¹)) =
  TF.com₂ α¹ , TF.com₂ β¹
TF.com₂ (idn (⟨-⊗-⟩ {A = A}{B})) =
  S.idnᵗ (G.homˢ A _) _ , S.idnᵗ (G.homˢ B _) _
TF.com₂ (cmp (⟨-⊗-⟩ {A = A}{B}) _ _) =
  S.idnᵗ (G.homˢ A _) _ , S.idnᵗ (G.homˢ B _) _
