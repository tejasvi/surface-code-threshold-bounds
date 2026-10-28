import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3128 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3128 = true := by
  decide +kernel

theorem tot3128 : totK PA10K2 A10K2.t3128 = [0, 0, 435690288822, 1735097205872, 2033197056859, 638394133770, 18757599771, 0, 0, 0] := by
  decide +kernel

theorem rows3129 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3129 = true := by
  decide +kernel

theorem tot3129 : totK PA10K2 A10K2.t3129 = [0, 0, 0, 721888100799, 2182462217418, 1567746889691, 251040823779, 6904928264, 0, 0] := by
  decide +kernel

theorem rows3130 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3130 = true := by
  decide +kernel

theorem tot3130 : totK PA10K2 A10K2.t3130 = [0, 0, 541429034706, 1843385315945, 1824570071941, 565452306588, 49972375802, 0, 0, 0] := by
  decide +kernel

theorem rows3131 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3131 = true := by
  decide +kernel

theorem tot3131 : totK PA10K2 A10K2.t3131 = [0, 0, 227291314947, 1256648690347, 2190106596100, 1211672296938, 115285335615, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
