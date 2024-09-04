
inductive Weekend where
  | saturday : Weekend
  | sunday : Weekend
  deriving Repr

open Weekend

def numberOfDay (d : Weekend) : Nat :=
  match d with
    | saturday => 6
    | sunday => 7

#print numberOfDay

#check Weekend.rec
#print Weekend.recOn
#print Weekend.casesOn

--------------------------------------------------------------------------------

def next (d : Weekend) : Weekend :=
  match d with
    | saturday => sunday
    | sunday => saturday

def previous (d : Weekend) : Weekend :=
  match d with
    | saturday => sunday
    | sunday => saturday

def next_previous (d : Weekend) : next (previous d) = d :=
  match d with
    | saturday => rfl
    | sunday => rfl

#eval saturday
#eval numberOfDay saturday


--------------------------------------------------------------------------------

namespace N1

-- Sum type
inductive S (α : Type u) (A : α -> Sort v) where
  | mk : (a : α) -> A a -> S α A

open Nat

def Seqz := S Nat (fun _ => Bool)

def oneOfThem : Seqz :=
  S.mk 0 true

def anotheOne : Seqz :=
  S.mk 1 false

inductive P (α : Type u) (A : α -> Sort v) where
  | mk : ((a : α) -> A a) -> P α A

def PNN := P Nat (fun _ => Nat)

def idP := P.mk (fun n => n + 1)

end N1

--------------------------------------------------------------------------------

namespace N2

-- universe u v

inductive Prodz (α : Type u) (β : Type v) where
  | mk (a : α) (b : β) : Prodz α β
  deriving Repr

def fst {α : Type u} {β : Type v} (p : Prod α β) : α :=
  match p with
    | Prod.mk a _ => a

def snd {α : Type u} {β : Type v} (p : Prod α β) : β :=
  match p with
    | Prod.mk _ b => b


-- rec is not there yet. Neither is recOn, but casesOn (or match) can be used
def sumzzz (pair : Prodz Nat Nat) : Nat :=
  Prodz.rec (α := Nat) (β := Nat) (motive := fun _ => Nat) (fun a b => a + b) pair

#check Prodz.casesOn

def sum_casesOn_verbose (ab : Prodz Nat Nat) : Nat :=
  Prodz.casesOn
    (α := Nat)
    (β := Nat)
    (motive := fun _ => Nat)
    ab
    (fun a b => a + b)

def sum_casesOn_test (ab : Prodz Nat Nat) : Nat :=
  ab.casesOn
    (α := Nat)
    (β := Nat)
    (motive := fun _ => Nat)
    (fun a b => a + b)

def sum_casesOn (pair : Prodz Nat Nat) : Nat :=
  pair.casesOn (fun a b => a + b)

#eval sum_casesOn (Prodz.mk 1 2)


inductive Sumz (α : Type u) (β: Type v) where
  | inl (a : α) : Sumz α β
  | inr (b : β) : Sumz α β


def zoo (a_or_b : Sumz Nat Bool) : Bool :=
  match a_or_b with
    | Sumz.inl _ => true
    | Sumz.inr b => b

def zooz(a_or_b : Sumz Nat Bool) : Bool :=
  a_or_b.casesOn (fun _ => true) (fun b => b)


inductive Color1 where
  | mk (red green blue : Nat) : Color1

structure Color2 where
  red : Nat
  green : Nat
  blue : Nat
  deriving Repr

#eval Color2.mk 0 255 0

def color : Color2 := { red := 0, green := 255, blue := 0}

structure Semigroup where
  carrier : Type u
  mul : carrier -> carrier -> carrier
  mul_assoc : ∀ (a b c : carrier), mul a (mul b c) = mul (mul a b) c

--------------------------------------------------------------------------------

inductive Option (α: Type u) where
  | some : α -> Option α
  | none : Option α
  deriving Repr

def yep? (n? : Option Nat) : Bool :=
  match n? with
    | Option.some _ => true
    | Option.none => false

#eval yep? Option.none
#eval yep? (Option.some 42)


def Partial α β := α -> Option β

def compose (f : Partial α β) (g : Partial β γ) : Partial α γ :=
  fun a =>
    match f a with
      | Option.none => Option.none
      | Option.some b => g b

def compose_assoc
  {f : Partial α β} {g : Partial β γ} {h : Partial γ δ} :
  compose f (compose g h) = compose (compose f g) h :=
  sorry -- not rfl :D

--------------------------------------------------------------------------------

inductive Inhabited (α : Type u) where
  | mk : α -> Inhabited α

def inhabited_nat : Inhabited Nat := Inhabited.mk 0

--------------------------------------------------------------------------------

open Nat

#print Nat

def add (m n : Nat) :=
  match n with
    | 0 => m
    | Nat.succ n => Nat.succ (add m n)

#eval add 5 7

theorem add_zero (m : Nat) : m + 0 = m := rfl

theorem add_succ (m n : Nat) : m + Nat.succ n = Nat.succ (m + n) := rfl

theorem zero_add (n : Nat) : 0 + n = n :=
  match n with
    | 0 => rfl
    | Nat.succ n => calc 0 + Nat.succ n
        _ = Nat.succ (0 + n) := rfl
        _ = Nat.succ n := by rw[zero_add n] -- and without tactics?

#print zero_add -- Have  a look at the expanded proof. Ah, congrArg!
-- theorem N2.zero_add : ∀ (n : Nat), 0 + n = n :=
-- fun n =>
--   Nat.brecOn n fun n f =>
--     (match (motive := ∀ (n : Nat), Nat.below n → 0 + n = n) n with
--       | 0 => fun x => rfl
--       | n.succ => fun x =>
--         trans (trans rfl rfl) (Eq.mpr (id (congrArg (fun _a => _a.succ = n.succ) x.fst.fst)) (Eq.refl n.succ)))
--       f

#check congrArg

theorem zero_add₂ (n : Nat) : 0 + n = n :=
   match n with
    | 0 => rfl
    | Nat.succ n => calc 0 + Nat.succ n
        _ = Nat.succ (0 + n) := rfl
        _ = Nat.succ n := congrArg Nat.succ (zero_add₂ n)


#check zero_add 42


theorem add_assoc : ∀ (m n p : Nat), (m + n) + p = m + (n + p) :=
  fun m n p =>
    match p with
      | 0 =>
          calc m + n + 0
          _ = m + n := add_zero (m + n)
          _ = m + (n + 0) := congrArg (m + ·) (add_zero n)
      | p + 1 =>
          calc m + n + (p + 1)
          _ = m + n + p + 1 := rfl
          _ = m + (n + p) + 1 := congrArg (· + 1) (add_assoc m n p)
          _ = m + (n + p + 1) := congrArg (m + ·) (Eq.refl (n+p+1))

theorem succ_add : ∀ (m n : Nat), m + n + 1 = m + 1 + n :=
  fun m n =>
    match n with
      | 0 => calc m + 0 + 1
          _ = m + 1 := congrArg (· + 1) (add_zero m)
          _ = m + 1 + 0 := add_zero (m + 1)
      | n + 1 => calc m + (n + 1) + 1
          _ = m + n + 1 + 1 := congrArg (· + 1) (add_assoc m n 1)
          _ = m + 1 + n + 1 := congrArg (· + 1) (succ_add m n)
          _ = m + 1 + (n + 1) := add_assoc (m + 1) n 1

theorem add_comm : ∀ (m n : Nat), m + n = n + m :=
  fun m n =>
    match n with
      | 0 => calc
          m + 0 = m     := add_zero m
          _     = 0 + m := (zero_add m).symm
      | n + 1 => calc m + (n + 1)
          _ = m + n + 1 := rfl
          _ = n + m + 1 := congrArg (· + 1) (add_comm m n)
          _ = (n + 1) + m := succ_add n m

--------------------------------------------------------------------------------

inductive List (α : Sort u) where
  | nil : List α
  | cons: α -> List α -> List α

open List


def append (as bs : List α) : List α :=
  match as with
    | nil => bs
    | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as :=
  rfl

theorem cons_append (as bs : List α) (a : α): append (cons a as) bs = cons a (append as bs) :=
  sorry

theorem append_nil (as : List α) : (append as nil) = as :=
  sorry

theorem append_assoc (as bs cs : List α) : append as (append bs cs) = append (append as bs) cs :=
  sorry

-- Try also defining the function length : {α : Type u} → List α → Nat that returns the length of a list, and prove that it behaves as expected (for example, length (append as bs) = length as + length bs).
