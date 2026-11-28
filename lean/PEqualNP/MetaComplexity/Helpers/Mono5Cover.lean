import PEqualNP.MetaComplexity.Helpers.Mono5Cover00
import PEqualNP.MetaComplexity.Helpers.Mono5Cover01
import PEqualNP.MetaComplexity.Helpers.Mono5Cover02
import PEqualNP.MetaComplexity.Helpers.Mono5Cover03
import PEqualNP.MetaComplexity.Helpers.Mono5Cover04
import PEqualNP.MetaComplexity.Helpers.Mono5Cover05
import PEqualNP.MetaComplexity.Helpers.Mono5Cover06
import PEqualNP.MetaComplexity.Helpers.Mono5Cover07
import PEqualNP.MetaComplexity.Helpers.Mono5Cover08
import PEqualNP.MetaComplexity.Helpers.Mono5Cover09
import PEqualNP.MetaComplexity.Helpers.Mono5Cover10
import PEqualNP.MetaComplexity.Helpers.Mono5Cover11

/-! Data of `L-meta-8613`, written by notes/data/table2/statements/mono5/lean_cover.py. The pieces assembled: every monotone table of five inputs is a listed table after relabelling. -/

namespace PEqualNP.MetaComplexity.Mono5

theorem monoTables_five : monoTables 5 = step 16 E4 (c00 ++ (c01 ++ (c02 ++ (c03 ++ (c04 ++ (c05 ++ (c06 ++ (c07 ++ (c08 ++ (c09 ++ (c10 ++ (c11)))))))))))) := by
  rw [← E4_split]
  show step 16 (monoTables 4) (monoTables 4) = _
  rw [monoTables_four]

theorem cover : ∀ t ∈ monoTables 5, Good reps t := by
  intro t ht
  rw [monoTables_five] at ht
  simp only [step_append, List.mem_append] at ht
  rcases ht with h | h | h | h | h | h | h | h | h | h | h | h
  · exact cover00 t h
  · exact cover01 t h
  · exact cover02 t h
  · exact cover03 t h
  · exact cover04 t h
  · exact cover05 t h
  · exact cover06 t h
  · exact cover07 t h
  · exact cover08 t h
  · exact cover09 t h
  · exact cover10 t h
  · exact cover11 t h

end PEqualNP.MetaComplexity.Mono5
