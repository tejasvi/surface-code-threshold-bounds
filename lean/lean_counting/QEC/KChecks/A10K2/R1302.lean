import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5208 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5208 = true := by
  decide +kernel

theorem tot5208 : totK PA10K2 A10K2.t5208 = [0, 280582103063, 1331917117537, 2054089124751, 1171690292728, 180071002941, 5459593153, 0, 0, 0] := by
  decide +kernel

theorem rows5209 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5209 = true := by
  decide +kernel

theorem tot5209 : totK PA10K2 A10K2.t5209 = [0, 369174955114, 1553969754061, 2089248804739, 973353506303, 115724911755, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5210 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5210 = true := by
  decide +kernel

theorem tot5210 : totK PA10K2 A10K2.t5210 = [0, 414718020177, 1702525534748, 2076354600551, 765795130766, 64214379686, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5211 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5211 = true := by
  decide +kernel

theorem tot5211 : totK PA10K2 A10K2.t5211 = [0, 0, 589315068144, 2058709506357, 1983194817897, 458535360889, 13816090359, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
