import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows848 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t848 = true := by
  decide +kernel

theorem tot848 : totK PA10K2 A10K2.t848 = [0, 253046812372, 1234710126137, 2045760918896, 1213650778256, 194441949798, 5624717336, 0, 0, 0] := by
  decide +kernel

theorem rows849 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t849 = true := by
  decide +kernel

theorem tot849 : totK PA10K2 A10K2.t849 = [0, 613409264780, 2029742299354, 1874456454897, 469800587610, 24978960967, 0, 0, 0, 0] := by
  decide +kernel

theorem rows850 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t850 = true := by
  decide +kernel

theorem tot850 : totK PA10K2 A10K2.t850 = [0, 0, 763649239927, 2239396246305, 1694280103941, 272142670535, 6281495166, 0, 0, 0] := by
  decide +kernel

theorem rows851 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t851 = true := by
  decide +kernel

theorem tot851 : totK PA10K2 A10K2.t851 = [76628528242, 87255542013, 340449122381, 1609588293308, 2134073457718, 749779471628, 56100664475, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
