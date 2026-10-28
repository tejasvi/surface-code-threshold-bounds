import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2496 = true := by
  decide +kernel

theorem tot2496 : totK PD2M8K2 D2M8K2.t2496 = [63020407318, 332431957529, 403700027950, 92539399019, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows2497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2497 = true := by
  decide +kernel

theorem tot2497 : totK PD2M8K2 D2M8K2.t2497 = [0, 207755561430, 492045730688, 181714665725, 7286232085, 0, 0, 0] := by
  decide +kernel

theorem rows2498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2498 = true := by
  decide +kernel

theorem tot2498 : totK PD2M8K2 D2M8K2.t2498 = [0, 196877681438, 468170015657, 213542954977, 14692331624, 0, 0, 0] := by
  decide +kernel

theorem rows2499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2499 = true := by
  decide +kernel

theorem tot2499 : totK PD2M8K2 D2M8K2.t2499 = [0, 191313691120, 462888959412, 206687796644, 12267505601, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
