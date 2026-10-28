import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6080 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6080 = true := by
  decide +kernel

theorem tot6080 : totK PA10K2 A10K2.t6080 = [0, 0, 525959843593, 1984164405014, 2125991407752, 519770930969, 18363904575, 0, 0, 0] := by
  decide +kernel

theorem rows6081 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6081 = true := by
  decide +kernel

theorem tot6081 : totK PA10K2 A10K2.t6081 = [0, 408659135851, 1378505147170, 1580602699125, 1046805609289, 469292158451, 50425690648, 0, 0, 0] := by
  decide +kernel

theorem rows6082 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6082 = true := by
  decide +kernel

theorem tot6082 : totK PA10K2 A10K2.t6082 = [0, 370669945331, 1645870469768, 2153418781403, 858452158297, 77534402549, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6083 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6083 = true := by
  decide +kernel

theorem tot6083 : totK PA10K2 A10K2.t6083 = [0, 0, 568332411612, 1961808882423, 1855193450467, 488015783375, 31306924438, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
