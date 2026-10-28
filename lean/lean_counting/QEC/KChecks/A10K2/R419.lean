import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1676 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1676 = true := by
  decide +kernel

theorem tot1676 : totK PA10K2 A10K2.t1676 = [0, 0, 535917147019, 1824345599313, 1806297908897, 471411496837, 40389715597, 0, 0, 0] := by
  decide +kernel

theorem rows1677 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1677 = true := by
  decide +kernel

theorem tot1677 : totK PA10K2 A10K2.t1677 = [0, 0, 307739496603, 1537024030043, 2097040412589, 702254040556, 43560737560, 0, 0, 0] := by
  decide +kernel

theorem rows1678 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1678 = true := by
  decide +kernel

theorem tot1678 : totK PA10K2 A10K2.t1678 = [0, 0, 213371739588, 1045946298764, 1933617466347, 1205426983423, 233528391130, 6354482628, 0, 0] := by
  decide +kernel

theorem rows1679 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1679 = true := by
  decide +kernel

theorem tot1679 : totK PA10K2 A10K2.t1679 = [0, 0, 458508014812, 1736768963045, 1970786144923, 558818726207, 32040661968, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
