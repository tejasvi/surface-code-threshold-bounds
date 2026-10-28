import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12564 = true := by
  decide +kernel

theorem tot12564 : totK PD2M8K2 D2M8K2.t12564 = [0, 0, 90563211903, 376349843887, 342869583519, 52145643458, 1053411165, 0] := by
  decide +kernel

theorem rows12565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12565 = true := by
  decide +kernel

theorem tot12565 : totK PD2M8K2 D2M8K2.t12565 = [0, 0, 0, 315325712099, 472620112308, 77669803607, 1021381562, 0] := by
  decide +kernel

theorem rows12566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12566 = true := by
  decide +kernel

theorem tot12566 : totK PD2M8K2 D2M8K2.t12566 = [0, 0, 185567760597, 439048937460, 220192384799, 40091544340, 2645825719, 0] := by
  decide +kernel

theorem rows12567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12567 = true := by
  decide +kernel

theorem tot12567 : totK PD2M8K2 D2M8K2.t12567 = [0, 0, 192631503186, 485728162873, 212287036002, 6663439011, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
