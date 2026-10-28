import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows168 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t168 = true := by
  decide +kernel

theorem tot168 : totK PA10K2 A10K2.t168 = [254943197349, 1209383316162, 2003468937859, 1241906438719, 201773035603, 5453753178, 0, 0, 0, 0] := by
  decide +kernel

theorem rows169 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t169 = true := by
  decide +kernel

theorem tot169 : totK PA10K2 A10K2.t169 = [373242481681, 1633861931712, 2163937794813, 861286864185, 71707134853, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows170 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t170 = true := by
  decide +kernel

theorem tot170 : totK PA10K2 A10K2.t170 = [207095436674, 978998681076, 1895453806061, 1538133562263, 344482951274, 19745625751, 0, 0, 0, 0] := by
  decide +kernel

theorem rows171 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t171 = true := by
  decide +kernel

theorem tot171 : totK PA10K2 A10K2.t171 = [439899752416, 1760822021334, 2034262772308, 625210041368, 40681057607, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
