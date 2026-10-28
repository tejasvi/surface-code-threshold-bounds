import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8136 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8136 = true := by
  decide +kernel

theorem tot8136 : totK PA10K2 A10K2.t8136 = [0, 0, 298738363490, 1244642865338, 1936464077686, 1211414015040, 192418431526, 0, 0, 0] := by
  decide +kernel

theorem rows8137 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8137 = true := by
  decide +kernel

theorem tot8137 : totK PA10K2 A10K2.t8137 = [0, 0, 467024804561, 1823122699018, 2031703738915, 604181386074, 30771235636, 0, 0, 0] := by
  decide +kernel

theorem rows8138 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8138 = true := by
  decide +kernel

theorem tot8138 : totK PA10K2 A10K2.t8138 = [0, 0, 0, 656172665710, 2067657947308, 1686558926511, 383609245939, 17754888877, 0, 0] := by
  decide +kernel

theorem rows8139 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8139 = true := by
  decide +kernel

theorem tot8139 : totK PA10K2 A10K2.t8139 = [0, 0, 281204290441, 1338575644906, 2058747117914, 1140325634976, 144208393049, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
