import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1688 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1688 = true := by
  decide +kernel

theorem tot1688 : totK PA10K2 A10K2.t1688 = [0, 0, 0, 547299411203, 1917226237212, 1770438235331, 433997579507, 31452573850, 0, 0] := by
  decide +kernel

theorem rows1689 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1689 = true := by
  decide +kernel

theorem tot1689 : totK PA10K2 A10K2.t1689 = [0, 0, 481676879802, 1681270017859, 1869067808148, 645748215351, 52376776708, 0, 0, 0] := by
  decide +kernel

theorem rows1690 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1690 = true := by
  decide +kernel

theorem tot1690 : totK PA10K2 A10K2.t1690 = [0, 0, 296845519927, 1529593619337, 2089276848321, 784764101859, 59339750188, 0, 0, 0] := by
  decide +kernel

theorem rows1691 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1691 = true := by
  decide +kernel

theorem tot1691 : totK PA10K2 A10K2.t1691 = [0, 0, 268061909688, 1134111778839, 1899242693526, 1193508477778, 221152359893, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
