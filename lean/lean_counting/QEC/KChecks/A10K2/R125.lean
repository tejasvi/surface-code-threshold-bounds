import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows500 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t500 = true := by
  decide +kernel

theorem tot500 : totK PA10K2 A10K2.t500 = [0, 460257217030, 1704016253560, 1867583443607, 688904954448, 71863511604, 0, 0, 0, 0] := by
  decide +kernel

theorem rows501 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t501 = true := by
  decide +kernel

theorem tot501 : totK PA10K2 A10K2.t501 = [0, 285378750548, 1476793792577, 2081053380247, 776025743754, 44995361554, 0, 0, 0, 0] := by
  decide +kernel

theorem rows502 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t502 = true := by
  decide +kernel

theorem tot502 : totK PA10K2 A10K2.t502 = [0, 298271261910, 1187970818054, 1897314210764, 1145026552276, 181589179945, 6239673734, 0, 0, 0] := by
  decide +kernel

theorem rows503 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t503 = true := by
  decide +kernel

theorem tot503 : totK PA10K2 A10K2.t503 = [0, 296697742459, 1462839863606, 2235923597765, 1012749231875, 92054016266, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
