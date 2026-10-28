import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows596 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t596 = true := by
  decide +kernel

theorem tot596 : totK PA10K2 A10K2.t596 = [0, 450019681657, 1655516154290, 1853662857828, 624896710293, 51782903379, 0, 0, 0, 0] := by
  decide +kernel

theorem rows597 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t597 = true := by
  decide +kernel

theorem tot597 : totK PA10K2 A10K2.t597 = [0, 0, 959856330187, 2378262219989, 1205755713118, 106683496047, 0, 0, 0, 0] := by
  decide +kernel

theorem rows598 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t598 = true := by
  decide +kernel

theorem tot598 : totK PA10K2 A10K2.t598 = [0, 424743448484, 1484694514194, 1882933623005, 996077452338, 193827742749, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows599 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t599 = true := by
  decide +kernel

theorem tot599 : totK PA10K2 A10K2.t599 = [0, 252951503060, 1362331525449, 2169859877885, 1162112998264, 132122561156, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
