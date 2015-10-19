{-# OPTIONS --without-K #-}

module Ambient.Groupoid.Tensor where

open import Agda.Primitive
import Ambient.Groupoid.Base as G
open import Ambient.Groupoid.Map as Map
open import Ambient.Groupoid.Tensor.Boot public
import Setoid as S
open import Type as T
  using (_,_)

infix 0 ⟨_,₀_⟩
infix 0 ⟨_⊗₀_⟩

π₀
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (A ⊗ B) Map.⇒₀ᵗ A
_$₀_ π₀ =
  T.Ten.π₀
-$₁ˢ- π₀ =
  S.Ten.π₀
idn (π₀ {A = A}) =
  λ {a} → S.idnᵗ (G.homˢ A (T.Ten.π₀ a , T.Ten.π₀ a)) _
cmp (π₀ {A = A}) =
  λ {a}{_}{c} _ _ → S.idnᵗ (G.homˢ A (T.Ten.π₀ a , T.Ten.π₀ c)) _

π₁
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (A ⊗ B) Map.⇒₀ᵗ B
_$₀_ π₁ =
  T.Ten.π₁
-$₁ˢ- π₁ =
  S.Ten.π₁
idn (π₁ {B = B}) =
  λ {a} → S.idnᵗ (G.homˢ B (T.Ten.π₁ a , T.Ten.π₁ a)) _
cmp (π₁ {B = B}) =
  λ {a}{_}{c} _ _ → S.idnᵗ (G.homˢ B (T.Ten.π₁ a , T.Ten.π₁ c)) _

⟨-,-⟩
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {X : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {A : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {B : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → ((X Map.⇒₀ᵍ A) ⊗ (X Map.⇒₀ᵍ B)) Map.⇒₀ᵗ (X Map.⇒₀ᵍ A ⊗ B)
_$₀_ (_$₀_ ⟨-,-⟩ FG) =
  T.Ten.⟨ T.Ten.π₀ FG $₀_ , T.Ten.π₁ FG $₀_ ⟩
-$₁ˢ- (_$₀_ ⟨-,-⟩ FG) =
  S.Ten.⟨-,-⟩ S.Map.$₀ (-$₁ˢ- (T.Ten.π₀ FG) , -$₁ˢ- (T.Ten.π₁ FG))
idn (_$₀_ ⟨-,-⟩ (F , G)) =
  Map.idn F , Map.idn G
cmp (_$₀_ ⟨-,-⟩ (F , G)) _ _ =
  cmp F _ _ , cmp G _ _
Map.com₁ (S.Map._$₀_ (-$₁ˢ- ⟨-,-⟩) (α , β)) =
  Map.com₁ α , Map.com₁ β
Map.nat₁ (S.Map._$₀_ (-$₁ˢ- ⟨-,-⟩) (α , β)) _ =
  Map.nat₁ α _ , Map.nat₁ β _
Map.com₂ (S.Map._$₁_ (-$₁ˢ- ⟨-,-⟩) (α¹ , β¹)) =
  Map.com₂ α¹ , Map.com₂ β¹
Map.com₂ (idn (⟨-,-⟩ {A = A}{B})) =
  S.idnᵗ (G.homˢ A _) _ , S.idnᵗ (G.homˢ B _) _
Map.com₂ (cmp (⟨-,-⟩ {A = A}{B}) _ _) =
  S.idnᵗ (G.homˢ A _) _ , S.idnᵗ (G.homˢ B _) _

⟨-⊗-⟩
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ ℓ₃ᵒ ℓ₃ˢᵒ ℓ₃ˢʰ}
  → {X₀ : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {X₁ : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {B : G.t d ℓ₃ᵒ ℓ₃ˢᵒ ℓ₃ˢʰ}
  → ((X₀ Map.⇒₀ᵍ A) ⊗ (X₁ Map.⇒₀ᵍ B)) Map.⇒₀ᵗ ((X₀ ⊗ X₁) Map.⇒₀ᵍ (A ⊗ B))
_$₀_ (_$₀_ ⟨-⊗-⟩ FG) =
  T.Ten.⟨ T.Ten.π₀ FG $₀_ ⊗ T.Ten.π₁ FG $₀_ ⟩
-$₁ˢ- (_$₀_ ⟨-⊗-⟩ FG) =
  S.Ten.⟨-⊗-⟩ S.Map.$₀ (-$₁ˢ- (T.Ten.π₀ FG) , -$₁ˢ- (T.Ten.π₁ FG))
idn (_$₀_ ⟨-⊗-⟩ (F , G)) =
  Map.idn F , Map.idn G
cmp (_$₀_ ⟨-⊗-⟩ (F , G)) _ _ =
  Map.cmp F _ _ , Map.cmp G _ _
Map.com₁ (S.Map._$₀_ (-$₁ˢ- ⟨-⊗-⟩) (α , β)) =
  Map.com₁ α , Map.com₁ β
Map.nat₁ (S.Map._$₀_ (-$₁ˢ- ⟨-⊗-⟩) (α , β)) _ =
  Map.nat₁ α _ , Map.nat₁ β _
Map.com₂ (S.Map._$₁_ (-$₁ˢ- ⟨-⊗-⟩) (α¹ , β¹)) =
  Map.com₂ α¹ , Map.com₂ β¹
Map.com₂ (idn (⟨-⊗-⟩ {A = A}{B})) =
  S.idnᵗ (G.homˢ A _) _ , S.idnᵗ (G.homˢ B _) _
Map.com₂ (cmp (⟨-⊗-⟩ {A = A}{B}) _ _) =
  S.idnᵗ (G.homˢ A _) _ , S.idnᵗ (G.homˢ B _) _

α : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → (A ⊗ B) ⊗ C Map.⇒₀ᵗ A ⊗ (B ⊗ C)
Map._$₀_ α ((a , b) , c) =
  a , (b , c)
S.Map._$₀_ (Map.-$₁ˢ- α) ((f , g) , h) =
  f , (g , h)
S.Map._$₁_ (Map.-$₁ˢ- α) ((p , q) , r) =
  p , (q , r)
Map.idn (α {A = A}{B}{C}) =
  S.idnᵗ (G.homˢ A _) _ , (S.idnᵗ (G.homˢ B _) _ , S.idnᵗ (G.homˢ C _) _)
Map.cmp (α {A = A}{B}{C}) _ _ =
  S.idnᵗ (G.homˢ A _) _ , (S.idnᵗ (G.homˢ B _) _ , S.idnᵗ (G.homˢ C _) _)

ap-lhs₀
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → (F : A ⊗ B Map.⇒₀ᵗ C)
  → (a : G.obj A)
  → B Map.⇒₀ᵗ C
Map._$₀_ (ap-lhs₀ F a) =
  T.Ten.ap-lhs (F Map.$₀_) a
Map.-$₁ˢ- (ap-lhs₀ {A = A} F a) =
  S.Ten.ap-lhs₀ (Map.-$₁ˢ- F) (G.idnˢ A S.Map.$₀ _)
Map.idn (ap-lhs₀ F a) =
  Map.idn F
Map.cmp (ap-lhs₀ {A = A}{B}{C} F a) g f =
  S.cmpᵗ (G.homˢ C _)
    ( Map.cmp F _ _
    , F Map.$₂
      ( S.invᵗ (G.homˢ A _) (G.idn-rhs A _)
      , S.idnᵗ (G.homˢ B _) _) )

ap-rhs₀
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {C : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → (F : A ⊗ B Map.⇒₀ᵗ C)
  → (b : G.obj B)
  → A Map.⇒₀ᵗ C
Map._$₀_ (ap-rhs₀ F b) =
  T.Ten.ap-rhs (F Map.$₀_) b
Map.-$₁ˢ- (ap-rhs₀ {B = B} F b) =
  S.Ten.ap-rhs₀ (Map.-$₁ˢ- F) (G.idnˢ B S.Map.$₀ _)
Map.idn (ap-rhs₀ F b) =
  Map.idn F
Map.cmp (ap-rhs₀ {A = A}{B}{C} F b) g f =
  S.cmpᵗ (G.homˢ C _)
    ( Map.cmp F _ _
    , F Map.$₂
        ( S.idnᵗ (G.homˢ A _) _
        , S.invᵗ (G.homˢ B _) (G.idn-rhs B _)) )

⟨_,₀_⟩
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {X : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {A : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {B : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → (F : X Map.⇒₀ᵗ A)
  → (G : X Map.⇒₀ᵗ B)
  → (X Map.⇒₀ᵗ A ⊗ B)
⟨ F ,₀ G ⟩ = ⟨-,-⟩ Map.$₀ (F , G)

⟨_⊗₀_⟩
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ ℓ₃ᵒ ℓ₃ˢᵒ ℓ₃ˢʰ}
  → {X₀ : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {X₁ : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A  : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {B  : G.t d ℓ₃ᵒ ℓ₃ˢᵒ ℓ₃ˢʰ}
  → (F  : X₀ Map.⇒₀ᵗ A)
  → (G  : X₁ Map.⇒₀ᵗ B)
  → ((X₀ ⊗ X₁) Map.⇒₀ᵗ (A ⊗ B))
⟨ F ⊗₀ G ⟩ = ⟨-⊗-⟩ Map.$₀ (F , G)

⟨_[_],₀_⟩
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ ℓ₃ᵒ ℓ₃ˢᵒ ℓ₃ˢʰ}
  → {X : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {A : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {B : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {R : G.t d ℓ₃ᵒ ℓ₃ˢᵒ ℓ₃ˢʰ}
  → (F : X Map.⇒₀ᵗ A)
  → (K : A ⊗ B Map.⇒₀ᵗ R)
  → (G : X Map.⇒₀ᵗ B)
  → (X Map.⇒₀ᵗ R)
⟨ F [ K ],₀ G ⟩ = K ∘₀ᵗ ⟨-,-⟩ Map.$₀ (F , G)

⟨_[_]⊗₀_⟩
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ ℓ₃ᵒ ℓ₃ˢᵒ ℓ₃ˢʰ ℓ₄ᵒ ℓ₄ˢᵒ ℓ₄ˢʰ}
  → {X₀ : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ}
  → {X₁ : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → {A  : G.t d ℓ₂ᵒ ℓ₂ˢᵒ ℓ₂ˢʰ}
  → {B  : G.t d ℓ₃ᵒ ℓ₃ˢᵒ ℓ₃ˢʰ}
  → {R  : G.t d ℓ₄ᵒ ℓ₄ˢᵒ ℓ₄ˢʰ}
  → (F  : X₀ Map.⇒₀ᵗ A)
  → (K  : A ⊗ B Map.⇒₀ᵗ R)
  → (G  : X₁ Map.⇒₀ᵗ B)
  → ((X₀ ⊗ X₁) Map.⇒₀ᵗ R)
⟨ F [ K ]⊗₀ G ⟩ = K ∘₀ᵗ ⟨-⊗-⟩ Map.$₀ (F , G)
