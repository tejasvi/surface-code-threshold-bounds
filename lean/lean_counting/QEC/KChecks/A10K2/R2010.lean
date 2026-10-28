import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8040 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8040 = true := by
  decide +kernel

theorem tot8040 : totK PA10K2 A10K2.t8040 = [0, 0, 0, 559217663538, 1915375465614, 1882350278365, 472179035647, 18601657154, 0, 0] := by
  decide +kernel

theorem rows8041 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8041 = true := by
  decide +kernel

theorem tot8041 : totK PA10K2 A10K2.t8041 = [0, 0, 0, 118334424620, 1035817536043, 2133125547700, 1366252017433, 255005044982, 12473006693, 0] := by
  decide +kernel

theorem rows8042 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8042 = true := by
  decide +kernel

theorem tot8042 : totK PA10K2 A10K2.t8042 = [0, 0, 0, 283557321311, 1347074999196, 2045544857043, 1131756869012, 136891941268, 0, 0] := by
  decide +kernel

theorem rows8043 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8043 = true := by
  decide +kernel

theorem tot8043 : totK PA10K2 A10K2.t8043 = [0, 0, 0, 307030755596, 1537594666279, 2207197622709, 907611075028, 63594693261, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
