import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6552 = true := by
  decide +kernel

theorem tot6552 : totK PD2M8K2 D2M8K2.t6552 = [0, 182380095760, 476074803471, 230597508516, 9401489568, 0, 0, 0] := by
  decide +kernel

theorem rows6553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6553 = true := by
  decide +kernel

theorem tot6553 : totK PD2M8K2 D2M8K2.t6553 = [147289589861, 366320440717, 275186101994, 108135630199, 6777858474, 0, 0, 0] := by
  decide +kernel

theorem rows6554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6554 = true := by
  decide +kernel

theorem tot6554 : totK PD2M8K2 D2M8K2.t6554 = [168228045180, 439659626275, 279936735094, 30219266960, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6555 = true := by
  decide +kernel

theorem tot6555 : totK PD2M8K2 D2M8K2.t6555 = [110427884955, 425820067332, 331292726856, 30186708154, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
