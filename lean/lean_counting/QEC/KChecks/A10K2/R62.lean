import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows248 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t248 = true := by
  decide +kernel

theorem tot248 : totK PA10K2 A10K2.t248 = [0, 0, 111833022044, 1315215101716, 2266188431012, 790346748636, 57935029211, 0, 0, 0] := by
  decide +kernel

theorem rows249 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t249 = true := by
  decide +kernel

theorem tot249 : totK PA10K2 A10K2.t249 = [0, 386810876066, 1259393701867, 1350591915871, 986662430839, 648551933939, 135599603508, 5976421810, 0, 0] := by
  decide +kernel

theorem rows250 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t250 = true := by
  decide +kernel

theorem tot250 : totK PA10K2 A10K2.t250 = [0, 426840442260, 1714636376036, 2026178641407, 726670982273, 57150474447, 0, 0, 0, 0] := by
  decide +kernel

theorem rows251 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t251 = true := by
  decide +kernel

theorem tot251 : totK PA10K2 A10K2.t251 = [0, 0, 560394187282, 1920631454815, 1810581225632, 481517781661, 30810868011, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
