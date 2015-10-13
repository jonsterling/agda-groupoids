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

infix 0 ⟨_,₀_⟩
infix 0 ⟨_⊗₀_⟩

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

α : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → (A ⊗ B) ⊗ C Π.⇒₀ᵗ A ⊗ (B ⊗ C)
Π._$₀_ α ((a , b) , c) =
  a , (b , c)
S.Π._$₀_ (Π.-$₁ˢ- α) ((f , g) , h) =
  f , (g , h)
S.Π._$₁_ (Π.-$₁ˢ- α) ((p , q) , r) =
  p , (q , r)
Π.idn (α {A = A}{B}{C}) =
  S.idnᵗ (G.homˢ A _) _ , (S.idnᵗ (G.homˢ B _) _ , S.idnᵗ (G.homˢ C _) _)
Π.cmp (α {A = A}{B}{C}) _ _ =
  S.idnᵗ (G.homˢ A _) _ , (S.idnᵗ (G.homˢ B _) _ , S.idnᵗ (G.homˢ C _) _)

ap-lhs₀
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → (F : A ⊗ B Π.⇒₀ᵗ C)
  → (a : G.obj A)
  → B Π.⇒₀ᵗ C
Π._$₀_ (ap-lhs₀ F a) =
  T.∐.ap-lhs (F Π.$₀_) a
Π.-$₁ˢ- (ap-lhs₀ {A = A} F a) =
  S.∐.ap-lhs₀ (Π.-$₁ˢ- F) (G.idnˢ A S.Π.$₀ _)
Π.idn (ap-lhs₀ F a) =
  Π.idn F
Π.cmp (ap-lhs₀ {A = A}{B}{C} F a) g f =
  S.cmpᵗ (G.homˢ C _)
    ( Π.cmp F _ _
    , F Π.$₂
      ( S.invᵗ (G.homˢ A _) (G.idn-rhs A _)
      , S.idnᵗ (G.homˢ B _) _) )

ap-rhs₀
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → (F : A ⊗ B Π.⇒₀ᵗ C)
  → (b : G.obj B)
  → A Π.⇒₀ᵗ C
Π._$₀_ (ap-rhs₀ F b) =
  T.∐.ap-rhs (F Π.$₀_) b
Π.-$₁ˢ- (ap-rhs₀ {B = B} F b) =
  S.∐.ap-rhs₀ (Π.-$₁ˢ- F) (G.idnˢ B S.Π.$₀ _)
Π.idn (ap-rhs₀ F b) =
  Π.idn F
Π.cmp (ap-rhs₀ {A = A}{B}{C} F b) g f =
  S.cmpᵗ (G.homˢ C _)
    ( Π.cmp F _ _
    , F Π.$₂
        ( S.idnᵗ (G.homˢ A _) _
        , S.invᵗ (G.homˢ B _) (G.idn-rhs B _)) )

⟨_,₀_⟩
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {X : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {A : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {B : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → (F : X Π.⇒₀ᵗ A)
  → (G : X Π.⇒₀ᵗ B)
  → (X Π.⇒₀ᵗ A ⊗ B)
⟨ F ,₀ G ⟩ = ⟨-,-⟩ Π.$₀ (F , G)

⟨_⊗₀_⟩
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ ℓ₃ᵒ ℓ₃ˢᵒ ℓ₃ˢʰ}
  → {X₀ : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {X₁ : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A  : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {B  : G.t d ℓ₃ᵒ ℓ₃ˢᵒ ℓ₃ˢʰ}
  → (F  : X₀ Π.⇒₀ᵗ A)
  → (G  : X₁ Π.⇒₀ᵗ B)
  → ((X₀ ⊗ X₁) Π.⇒₀ᵗ (A ⊗ B))
⟨ F ⊗₀ G ⟩ = ⟨-⊗-⟩ Π.$₀ (F , G)

⟨_[_],₀_⟩
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ ℓ₃ᵒ ℓ₃ˢᵒ ℓ₃ˢʰ}
  → {X : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {A : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {B : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {R : G.t d ℓ₃ᵒ ℓ₃ˢᵒ ℓ₃ˢʰ}
  → (F : X Π.⇒₀ᵗ A)
  → (K : A ⊗ B Π.⇒₀ᵗ R)
  → (G : X Π.⇒₀ᵗ B)
  → (X Π.⇒₀ᵗ R)
⟨ F [ K ],₀ G ⟩ = K ∘₀ᵗ ⟨-,-⟩ Π.$₀ (F , G)

⟨_[_]⊗₀_⟩
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ ℓ₃ᵒ ℓ₃ˢᵒ ℓ₃ˢʰ ℓ₄ᵒ ℓ₄ˢᵒ ℓ₄ˢʰ}
  → {X₀ : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {X₁ : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A  : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {B  : G.t d ℓ₃ᵒ ℓ₃ˢᵒ ℓ₃ˢʰ}
  → {R  : G.t d ℓ₄ᵒ ℓ₄ˢᵒ ℓ₄ˢʰ}
  → (F  : X₀ Π.⇒₀ᵗ A)
  → (K  : A ⊗ B Π.⇒₀ᵗ R)
  → (G  : X₁ Π.⇒₀ᵗ B)
  → ((X₀ ⊗ X₁) Π.⇒₀ᵗ R)
⟨ F [ K ]⊗₀ G ⟩ = K ∘₀ᵗ ⟨-⊗-⟩ Π.$₀ (F , G)
