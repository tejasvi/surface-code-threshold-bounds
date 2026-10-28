import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2380 = true := by
  decide +kernel

theorem tot2380 : totK PD2M8K2 D2M8K2.t2380 = [0, 158970143308, 447334183604, 272289544350, 23620279184, 0, 0, 0] := by
  decide +kernel

theorem rows2381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2381 = true := by
  decide +kernel

theorem tot2381 : totK PD2M8K2 D2M8K2.t2381 = [0, 182261201038, 470115370661, 251289278193, 16828751003, 0, 0, 0] := by
  decide +kernel

theorem rows2382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2382 = true := by
  decide +kernel

theorem tot2382 : totK PD2M8K2 D2M8K2.t2382 = [0, 0, 262385442235, 502810399616, 122761298474, 1268739303, 0, 0] := by
  decide +kernel

theorem rows2383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2383 = true := by
  decide +kernel

theorem tot2383 : totK PD2M8K2 D2M8K2.t2383 = [0, 0, 181019388762, 482344774709, 214956971205, 8667190702, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
