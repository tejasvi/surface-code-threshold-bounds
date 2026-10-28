import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1428 = true := by
  decide +kernel

theorem tot1428 : totK PD2M8K2 D2M8K2.t1428 = [0, 0, 0, 233134621375, 466137881560, 139775047193, 5134755853, 0] := by
  decide +kernel

theorem rows1429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1429 = true := by
  decide +kernel

theorem tot1429 : totK PD2M8K2 D2M8K2.t1429 = [0, 0, 139663845658, 439538092281, 261680026925, 24272958920, 0, 0] := by
  decide +kernel

theorem rows1430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1430 = true := by
  decide +kernel

theorem tot1430 : totK PD2M8K2 D2M8K2.t1430 = [0, 0, 214554354291, 479554938022, 167341491468, 7355951982, 0, 0] := by
  decide +kernel

theorem rows1431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1431 = true := by
  decide +kernel

theorem tot1431 : totK PD2M8K2 D2M8K2.t1431 = [0, 0, 202530700073, 474455640405, 203683781334, 11448224421, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
