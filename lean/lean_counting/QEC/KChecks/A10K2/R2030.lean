import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8120 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8120 = true := by
  decide +kernel

theorem tot8120 : totK PA10K2 A10K2.t8120 = [0, 0, 203694454938, 860503735345, 1572536317049, 1695362746642, 670616801855, 57551169768, 0, 0] := by
  decide +kernel

theorem rows8121 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8121 = true := by
  decide +kernel

theorem tot8121 : totK PA10K2 A10K2.t8121 = [0, 0, 523170312621, 1844028132272, 1928840163836, 500199396114, 26273936808, 0, 0, 0] := by
  decide +kernel

theorem rows8122 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8122 = true := by
  decide +kernel

theorem tot8122 : totK PA10K2 A10K2.t8122 = [0, 0, 84169918459, 882388334517, 2038182959457, 1524557010946, 362236977684, 18722998264, 0, 0] := by
  decide +kernel

theorem rows8123 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8123 = true := by
  decide +kernel

theorem tot8123 : totK PA10K2 A10K2.t8123 = [0, 0, 272837281739, 1157896376469, 1931568139544, 1314337287697, 195313206937, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
