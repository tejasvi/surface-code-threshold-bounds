import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2224 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2224 = true := by
  decide +kernel

theorem tot2224 : totK PA10K2 A10K2.t2224 = [0, 68910543473, 869009882498, 2056514330250, 1542713530029, 370088691154, 25680132735, 0, 0, 0] := by
  decide +kernel

theorem rows2225 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2225 = true := by
  decide +kernel

theorem tot2225 : totK PA10K2 A10K2.t2225 = [0, 211208261646, 948371668804, 1939015166956, 1488068727505, 254338942674, 5626791703, 0, 0, 0] := by
  decide +kernel

theorem rows2226 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2226 = true := by
  decide +kernel

theorem tot2226 : totK PA10K2 A10K2.t2226 = [0, 345497897871, 1715617975586, 2090550689280, 610914981128, 32569280177, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2227 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2227 = true := by
  decide +kernel

theorem tot2227 : totK PA10K2 A10K2.t2227 = [0, 200310298568, 1065912253709, 1995238531338, 1281979637251, 202259273968, 6239673734, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
