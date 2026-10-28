import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11864 = true := by
  decide +kernel

theorem tot11864 : totK PD2M8K2 D2M8K2.t11864 = [194070037291, 469902187314, 223601852434, 12534051746, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11865 = true := by
  decide +kernel

theorem tot11865 : totK PD2M8K2 D2M8K2.t11865 = [44110965194, 318234473092, 429887578622, 97693954641, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows11866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11866 = true := by
  decide +kernel

theorem tot11866 : totK PD2M8K2 D2M8K2.t11866 = [51740771055, 346083707581, 451773271356, 58762254520, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11867 = true := by
  decide +kernel

theorem tot11867 : totK PD2M8K2 D2M8K2.t11867 = [200686189571, 475175014439, 209201148537, 9847636232, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
