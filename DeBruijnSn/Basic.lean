
inductive Term : Type where
| var : Nat → Term
| app : Term → Term → Term
| lam : Term → Term

-- Ok so let's have this be computational
-- We follow https://hal.science/hal-00384683/document
def φ (j i : Nat) : Term → Term
| .var n => if n < i then .var n else .var $ n + j
| .app t u => .app (φ j i t) (φ j i u)
| .lam t => .lam $ φ j (i+1) t

set_option hygiene false

-- idk about these precedences
notation " [ " i:max " / " u:60 " ] " t:60 => (subst i u t)

def subst (i : Nat) (u : Term) : Term → Term
| .var n =>
  if n < i then .var n
  else if n = i then φ i 0 u
  else .var $ n - 1
| .app t₁ t₂ => .app ([i/u]t₁) ([i/u]t₂)
| .lam t => .lam $ [(i+1)/u]t

notation t:60 " ⟶ " t':60 => (Red t t')

inductive Red : Term → Term → Type where
| beta : (.app (.lam t) u) ⟶ [0/u]t
| congApp₁ : t ⟶ t' → (.app t u) ⟶ (.app t' u)
| congApp₂ : u ⟶ u' → (.app t u) ⟶ (.app t u')
| congLam : t ⟶ t' → (.lam t) ⟶ (.lam t')

notation t:60 " ⟶* " t':60 => (RedStar t t')

inductive RedStar : Term → Term → Type :=
| done : t ⟶* t
| step : t₁ ⟶ t₂ → t₂ ⟶* t₃ → t₁ ⟶* t₃

mutual
inductive Neutral : Term → Type where
| varNe : Neutral $ .var n
| appNe : Neutral ne → Normal t → Neutral (.app ne t)
inductive Normal : Term → Type where
| neutralNorm : Neutral ne → Normal ne
| lambdaNorm : Normal t → Normal (.lam t)
end

-- Weak head expansion: a family of "necessary reductions for normalization"
inductive WeakHeadExp : Term → Term → Term → Type where
| headWH : WeakHeadExp (.app (.lam t) u) ([0/u]t) u
| appWH : WeakHeadExp t t' u → WeakHeadExp (.app t v) (.app t' v) u

inductive SN : Term → Type where
| normSN : Normal t → SN t
| weakHeadSN : SN t' → SN u → WeakHeadExp t t' u → SN t

inductive Ty where
| base : Ty
| arrow : Ty → Ty → Ty

infix:60 " ⇒ " => Ty.arrow

notation "Ctx" => (List Ty)

#check List.get?
#print Option

notation ctx:50 " ⊢ " t:50 " :+ " ty:50 => (TypeTerm ctx t ty)
inductive TypeTerm : Ctx → Term → Ty → Type where
| varTy : ∀ Γ A n, Γ.get? n = .some A →  Γ ⊢ .var n :+ A
| appTy : ∀ Γ A B t u, Γ ⊢ t :+ A ⇒ B → Γ ⊢ u :+ A → Γ ⊢ .app t u :+ B
| lamTy : ∀ Γ A t, (A :: Γ) ⊢ t :+ B → Γ ⊢ .lam t :+ A ⇒ B

notation "⟦" ty "⟧" => (interpTy ty)

def interpTy : Ty → Term → Type
| .base => SN
| ty₁ ⇒ ty₂ => λ t ↦ ∀ u, ⟦ty₁⟧ u → ⟦ty₂⟧ (.app t u)
