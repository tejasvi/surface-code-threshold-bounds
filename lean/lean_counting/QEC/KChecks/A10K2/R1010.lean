import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4040 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4040 = true := by
  decide +kernel

theorem tot4040 : totK PA10K2 A10K2.t4040 = [0, 0, 76628528242, 436080142606, 1636950000949, 2069774207517, 712521780073, 55043167628, 0, 0] := by
  decide +kernel

theorem rows4041 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4041 = true := by
  decide +kernel

theorem tot4041 : totK PA10K2 A10K2.t4041 = [0, 0, 513529382586, 1914264546148, 1892893972262, 448763000328, 25686058060, 0, 0, 0] := by
  decide +kernel

theorem rows4042 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4042 = true := by
  decide +kernel

theorem tot4042 : totK PA10K2 A10K2.t4042 = [0, 0, 187252157681, 1105798527253, 2102495561225, 1325534523781, 256493922482, 13364899180, 0, 0] := by
  decide +kernel

theorem rows4043 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4043 = true := by
  decide +kernel

theorem tot4043 : totK PA10K2 A10K2.t4043 = [0, 0, 265289717592, 1130723367762, 1924012524084, 1356120219822, 206230717248, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
