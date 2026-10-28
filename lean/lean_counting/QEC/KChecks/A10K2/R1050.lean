import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4200 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4200 = true := by
  decide +kernel

theorem tot4200 : totK PA10K2 A10K2.t4200 = [0, 212862030042, 1061714077429, 1911725893125, 1318726168925, 217000206902, 5447185874, 0, 0, 0] := by
  decide +kernel

theorem rows4201 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4201 = true := by
  decide +kernel

theorem tot4201 : totK PA10K2 A10K2.t4201 = [0, 461089237715, 1651649409568, 1936207283675, 651986192330, 51464731716, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4202 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4202 = true := by
  decide +kernel

theorem tot4202 : totK PA10K2 A10K2.t4202 = [0, 96072695648, 1215628625973, 2312609667572, 1044227435139, 86064061578, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4203 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4203 = true := by
  decide +kernel

theorem tot4203 : totK PA10K2 A10K2.t4203 = [0, 333816047751, 1245038850090, 1849335550875, 1107382233002, 214030332282, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
