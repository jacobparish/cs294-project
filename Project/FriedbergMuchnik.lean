module

public import Project.OracleCode
public import Project.Queries

namespace Computability

def seq : ℕ → (Finset ℕ × Finset ℕ) × List ℕ
  | 0 => ((∅, ∅), [])
  | n + 1 => sorry

end Computability
