import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10232 = true := by
  decide +kernel

theorem tot10232 : totK PD2M8K2 D2M8K2.t10232 = [0, 167341020191, 446007776357, 281920764758, 30618259789, 0, 0, 0] := by
  decide +kernel

theorem rows10233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10233 = true := by
  decide +kernel

theorem tot10233 : totK PD2M8K2 D2M8K2.t10233 = [0, 157636110170, 462698139336, 268767189777, 18576529552, 0, 0, 0] := by
  decide +kernel

theorem rows10234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10234 = true := by
  decide +kernel

theorem tot10234 : totK PD2M8K2 D2M8K2.t10234 = [0, 0, 219799635802, 496720971313, 175802305673, 7229436959, 0, 0] := by
  decide +kernel

theorem rows10235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10235 = true := by
  decide +kernel

theorem tot10235 : totK PD2M8K2 D2M8K2.t10235 = [0, 66330446293, 290607598720, 395180315084, 121506194878, 5029857939, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
