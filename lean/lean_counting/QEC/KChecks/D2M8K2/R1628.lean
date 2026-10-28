import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6512 = true := by
  decide +kernel

theorem tot6512 : totK PD2M8K2 D2M8K2.t6512 = [0, 271953617055, 508175461590, 111326845599, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows6513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6513 = true := by
  decide +kernel

theorem tot6513 : totK PD2M8K2 D2M8K2.t6513 = [107477068962, 382675925837, 375595306478, 51904561460, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6514 = true := by
  decide +kernel

theorem tot6514 : totK PD2M8K2 D2M8K2.t6514 = [196663862542, 472404396888, 226712440607, 15455336545, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6515 = true := by
  decide +kernel

theorem tot6515 : totK PD2M8K2 D2M8K2.t6515 = [110345192872, 435872018747, 331343386087, 37409007564, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
