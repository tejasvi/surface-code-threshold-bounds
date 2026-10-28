import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t12 = true := by
  decide +kernel

theorem tot12 : totK PA10K2 A10K2.t12 = [0, 492132633152, 1792671126694, 1866781246283, 516075988040, 31608797364, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t13 = true := by
  decide +kernel

theorem tot13 : totK PA10K2 A10K2.t13 = [0, 114960938496, 1252684663989, 2247739181962, 895490623299, 65326404304, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t14 = true := by
  decide +kernel

theorem tot14 : totK PA10K2 A10K2.t14 = [0, 427933014809, 1471099541034, 1824551972882, 924914361244, 153851967938, 5546304973, 0, 0, 0] := by
  decide +kernel

theorem rows15 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t15 = true := by
  decide +kernel

theorem tot15 : totK PA10K2 A10K2.t15 = [115575618874, 601188090900, 1619128324915, 1937565050968, 712454533658, 55986814598, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
