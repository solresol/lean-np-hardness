import LeanNPHardness.CNFEncoding

/-!
# Unary-index encoding of CNF formulas

A literal on variable `v` is a polarity symbol followed by `v` marks, a
clause is its literals followed by an end marker, and a formula is the
concatenation of its clauses. Every symbol string is parsed by a small
automaton, giving a checked `FinEncoding` whose input size is the total
number of symbols. This encoding is the output format of the Cook--Levin
generator machine; the conversion to the binary framed encoding
`Formula.finEncoding` is a separate machine.
-/

namespace LeanNPHardness.CNF.Unary

/-- The unary CNF alphabet. -/
inductive Sym
  | mark
  | pos
  | neg
  | endClause
  deriving DecidableEq, Fintype, Repr

def encodeLiteral : Literal ℕ → List Sym
  | .positive v => .pos :: List.replicate v .mark
  | .negative v => .neg :: List.replicate v .mark

def encodeClause (clause : Clause ℕ) : List Sym :=
  clause.flatMap encodeLiteral ++ [.endClause]

def encode (formula : Formula ℕ) : List Sym :=
  formula.flatMap encodeClause

/-- Increment the variable of a literal. -/
def Literal.succVar : Literal ℕ → Literal ℕ
  | .positive v => .positive (v + 1)
  | .negative v => .negative (v + 1)

/-- Add to the variable of a literal. -/
def Literal.addVar (n : ℕ) : Literal ℕ → Literal ℕ
  | .positive v => .positive (v + n)
  | .negative v => .negative (v + n)

/-- Parse with the literals of the current clause (most recent first) and
the completed clauses (most recent first). -/
def parseAux : List Sym → List (Literal ℕ) → List (Clause ℕ) → Option (Formula ℕ)
  | [], [], acc => some acc.reverse
  | [], _ :: _, _ => none
  | .mark :: rest, l :: lits, acc => parseAux rest (Literal.succVar l :: lits) acc
  | .mark :: _, [], _ => none
  | .pos :: rest, lits, acc => parseAux rest (.positive 0 :: lits) acc
  | .neg :: rest, lits, acc => parseAux rest (.negative 0 :: lits) acc
  | .endClause :: rest, lits, acc => parseAux rest [] (lits.reverse :: acc)

def decode (symbols : List Sym) : Option (Formula ℕ) := parseAux symbols [] []

theorem parseAux_marks (v : ℕ) (rest : List Sym) (l : Literal ℕ) (lits : List (Literal ℕ))
    (acc : List (Clause ℕ)) :
    parseAux (List.replicate v .mark ++ rest) (l :: lits) acc =
      parseAux rest (Literal.addVar v l :: lits) acc := by
  induction v generalizing l with
  | zero => cases l <;> simp [Literal.addVar]
  | succ v ih =>
      rw [List.replicate_succ, List.cons_append, parseAux, ih]
      cases l <;> simp [Literal.addVar, Literal.succVar, Nat.add_comm, Nat.add_left_comm]

theorem parseAux_literal (l : Literal ℕ) (rest : List Sym) (lits : List (Literal ℕ))
    (acc : List (Clause ℕ)) :
    parseAux (encodeLiteral l ++ rest) lits acc = parseAux rest (l :: lits) acc := by
  cases l with
  | positive v =>
      simp only [encodeLiteral, List.cons_append, parseAux]
      rw [parseAux_marks]
      simp [Literal.addVar]
  | negative v =>
      simp only [encodeLiteral, List.cons_append, parseAux]
      rw [parseAux_marks]
      simp [Literal.addVar]

theorem parseAux_literals (clause : Clause ℕ) (rest : List Sym) (lits : List (Literal ℕ))
    (acc : List (Clause ℕ)) :
    parseAux (clause.flatMap encodeLiteral ++ rest) lits acc =
      parseAux rest (clause.reverse ++ lits) acc := by
  induction clause generalizing lits with
  | nil => simp
  | cons l clause ih =>
      rw [List.flatMap_cons, List.append_assoc, parseAux_literal, ih]
      simp

theorem parseAux_clause (clause : Clause ℕ) (rest : List Sym) (acc : List (Clause ℕ)) :
    parseAux (encodeClause clause ++ rest) [] acc = parseAux rest [] (clause :: acc) := by
  rw [encodeClause, List.append_assoc, parseAux_literals]
  simp [parseAux]

theorem parseAux_formula (formula : Formula ℕ) (rest : List Sym) (acc : List (Clause ℕ)) :
    parseAux (encode formula ++ rest) [] acc = parseAux rest [] (formula.reverse ++ acc) := by
  induction formula generalizing acc with
  | nil => simp [encode]
  | cons clause formula ih =>
      rw [encode, List.flatMap_cons, List.append_assoc, parseAux_clause, ← encode, ih]
      simp

@[simp]
theorem decode_encode (formula : Formula ℕ) : decode (encode formula) = some formula := by
  have := parseAux_formula formula [] []
  rw [List.append_nil] at this
  simp [decode, this, parseAux]

/-- The unary-index CNF encoding. -/
def finEncoding : Computability.FinEncoding (Formula ℕ) where
  Γ := Sym
  encode := encode
  decode := decode
  decode_encode := decode_encode
  ΓFin := inferInstance

@[simp]
theorem finEncoding_encode (formula : Formula ℕ) : finEncoding.encode formula = encode formula :=
  rfl

theorem encode_append (left right : Formula ℕ) :
    encode (left ++ right) = encode left ++ encode right := by
  simp [encode]

@[simp]
theorem encode_nil : encode [] = [] := rfl

theorem encode_cons (clause : Clause ℕ) (formula : Formula ℕ) :
    encode (clause :: formula) = encodeClause clause ++ encode formula := by
  simp [encode]

/-- CNF-SAT under the unary-index encoding. -/
def encodedUnarySAT : EncodedLanguage (Formula ℕ) where
  encoding := finEncoding
  accepts := SAT

/-- Exact 3-SAT under the unary-index encoding. -/
def encodedUnaryExactThreeSAT : EncodedLanguage (Formula ℕ) where
  encoding := finEncoding
  accepts := ExactThreeSAT

end LeanNPHardness.CNF.Unary
