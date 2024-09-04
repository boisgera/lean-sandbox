def i := 1
def j := i + 42

def b := true

def b2 := b && b
def b3 := b || b
def b4 := !b

def s := "Hello!"
def name := "Sébastien"
def greet := s ++ name

/- ------------------------------------- -/

def inc : (Nat → Nat) := (λ n ↦ n+1)
def forty_two := inc 41

def add : Nat → Nat → Nat := λ m ↦ λ n ↦ m + n

def add2 (m n : Nat) := m + n

/- ---------------------------------------- -/

def pair : Bool × Bool := (true, false)

def and7 (b: Bool × Bool)  := b.1 && b.2

def xorX (b₁b₂ : Bool × Bool) :=
  (b₁b₂.1 && !b₁b₂.2) || (!b₁b₂.1 && b₁b₂.2)

def g := xorX (true, true)

/- ---------------------------------------- -/

-- #check Nat
-- #check Type
/-
#check (Nat → Type) × Nat


def α : Type := Nat
#check List α
def β := Type
#check List β

def Prodz (α β : Type) := α × β
-/


#check List
#check List.nil
#check List.cons
#check List.elem
