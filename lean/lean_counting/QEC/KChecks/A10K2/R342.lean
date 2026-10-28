import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1368 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1368 = true := by
  decide +kernel

theorem tot1368 : totK PA10K2 A10K2.t1368 = [0, 0, 0, 42105865362, 751460116120, 2111032547222, 1351174142412, 199083392831, 5546304973, 0] := by
  decide +kernel

theorem rows1369 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1369 = true := by
  decide +kernel

theorem tot1369 : totK PA10K2 A10K2.t1369 = [0, 0, 0, 613209886970, 2127416526249, 1887927026275, 371094652882, 20094979411, 0, 0] := by
  decide +kernel

theorem rows1370 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1370 = true := by
  decide +kernel

theorem tot1370 : totK PA10K2 A10K2.t1370 = [0, 0, 308148872480, 1150914916105, 1670015087813, 1321530635331, 481232173455, 36938587266, 0, 0] := by
  decide +kernel

theorem rows1371 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1371 = true := by
  decide +kernel

theorem tot1371 : totK PA10K2 A10K2.t1371 = [0, 0, 489921636816, 1881318845742, 2010674618855, 507837396849, 18560348465, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
