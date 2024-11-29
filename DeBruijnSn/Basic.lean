


inductive Term : Type where
| var : Nat → Term
| app : Term → Term → Term
| lam : Term → Term

inductive Ren : Type where
| idR : Ren
| compR : Ren → Ren → Ren
| lift : Ren

inductive Subst : Type where
| idS : Subst
| comp : Subst → Ren → Subst
| cons : Term → Subst → Subst

infix:40 " ∘ " => Subst.comp
notation "↑" => Ren.lift
infix:80 " ⬝ " => Subst.cons

set_option hygiene false

-- idk about these precedences
notation t:60 " ⟨ " s:60 " ⟩ " => (subst s t)

def renVar (n : Nat) : Ren → Nat
| .idR => n
| .compR ρ₁ ρ₂ => renVar (renVar n ρ₁) ρ₂
| ↑ => n+1

def renTerm (ρ : Ren) : Term → Term
| .var n => .var $ renVar n ρ
| .app t₁ t₂ => .app (renTerm ρ t₁) (renTerm ρ t₂)
| .lam t => .lam (renTerm (.compR ρ ↑) t)

def substVar (n : Nat) : Subst → Term
| .idS => .var n
| t ⬝ σ => if n = 0 then t else substVar (n-1) σ
| .comp σ ρ => (renTerm ρ (substVar n σ))

def subst (σ : Subst) : Term → Term
| .var n => substVar n σ
| .app t₁ t₂ => .app (t₁⟨σ⟩) (t₂⟨σ⟩)
| .lam t => .lam (t⟨ (.var 0) ⬝ (σ ∘ ↑) ⟩)

notation t:60 " ⟶ " t':60 => (Red t t')

inductive Red : Term → Term → Type where
| beta : (.app (.lam t) u) ⟶ t⟨u ⬝ .idS⟩
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
| headWH : WeakHeadExp (.app (.lam t) u) (t⟨u⬝.idS⟩) u
| appWH : WeakHeadExp t t' u → WeakHeadExp (.app t v) (.app t' v) u

inductive SN : Term → Type where
| normSN : Normal t → SN t
| weakHeadSN : SN t' → SN u → WeakHeadExp t t' u → SN t

inductive Ty where
| base : Ty
| arrow : Ty → Ty → Ty

infix:60 " ⇒ " => Ty.arrow

notation "Ctx" => (List Ty)

notation ctx:50 " ⊢ " t:50 " :+ " ty:50 => (TypeTerm ctx t ty)
inductive TypeTerm : Ctx → Term → Ty → Type where
| varTy : ∀ Γ A n, Γ.get? n = .some A →  Γ ⊢ .var n :+ A
| appTy : ∀ Γ A B t u, Γ ⊢ t :+ A ⇒ B → Γ ⊢ u :+ A → Γ ⊢ .app t u :+ B
| lamTy : ∀ Γ A t, (A :: Γ) ⊢ t :+ B → Γ ⊢ .lam t :+ A ⇒ B

notation "⟦" ty "⟧" => (interpTy ty)

def interpTy : Ty → Term → Type
| .base => SN
| ty₁ ⇒ ty₂ => λ t ↦ ∀ u, ⟦ty₁⟧ u → ⟦ty₂⟧ (.app t u)

def compRenL (ρ : Ren) (σ: Subst) : Subst :=
match ρ, σ with
| .idR, _ => σ
| ↑, _⬝ σ' => σ'
| .compR ρ₁ ρ₂, _ => compRenL ρ₁ (compRenL ρ₂ σ)
| _, .idS => .comp .idS ρ
| ρ, .comp σ' ρ' => .comp (compRenL ρ σ') ρ' --ugh

def compSubst (σ τ : Subst) : Subst :=
match σ, τ with
| u⬝σ', τ => u⟨τ⟩ ⬝ (compSubst σ' τ)
| .idS, _ => τ
| _, .idS => σ
| .comp σ' ρ, τ => compSubst σ' (compRenL ρ τ)

theorem subst_var_comp : subst σ (substVar x τ) = substVar x (compSubst τ σ) :=
by sorry

theorem comp_assoc : t⟨compSubst σ (τ ∘ ρ)⟩ = t⟨(compSubst σ τ ∘ ρ)⟩ :=
by
  cases σ <;> simp [compSubst]
  case comp => sorry
  case cons t' σ' => sorry

theorem subst_comp : t⟨σ⟩⟨τ⟩ = t⟨compSubst σ τ⟩ :=
by
  cases t <;> simp [subst]
  case var => apply subst_var_comp
  case app => constructor <;> apply subst_comp
  case lam =>
    rw [subst_comp]
    simp [compSubst, subst, substVar, compRenL]
    sorry

theorem substShift : t⟨.var 0 ⬝ (σ ∘ ↑)⟩ = t⟨σ⟩ :=
by
  revert σ
  cases t <;> simp [subst] <;> intros σ
  case var => simp [substVar]; sorry
  case app => sorry
  case lam => sorry

theorem substIdS : t⟨.idS⟩ = t :=
by
  cases t <;> simp [subst, substVar]
  case app => constructor <;> apply substIdS
  case lam => sorry

theorem compSubstIdL : compSubst .idS σ = σ :=
by
  cases σ <;> simp [compSubst]

theorem compSubstIdR : compSubst σ .idS = σ :=
by
  cases σ <;> simp [compSubst]
  case cons =>
    constructor
    . simp [subst]
    sorry

theorem comp_lift : compSubst (.var 0 ⬝ (σ ∘ ↑)) (t ⬝ .idS) = t ⬝ σ :=
by
  simp [compSubst, compRenL, subst, substVar]
  apply compSubstIdR

theorem subst_subst : t⟨(.var 0 ⬝ (σ ∘ ↑))⟩⟨u⬝.idS⟩ = t⟨u⬝σ⟩ :=
by
  rw [subst_comp, comp_lift]

theorem app_subst : (.app ((.lam t)⟨σ⟩) u) ⟶ t⟨u⬝σ⟩ :=
by
  rw [← subst_subst]
  simp [subst]
  apply Red.beta
