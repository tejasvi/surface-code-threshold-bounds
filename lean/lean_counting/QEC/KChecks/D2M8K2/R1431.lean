import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5724 = true := by
  decide +kernel

theorem tot5724 : totK PD2M8K2 D2M8K2.t5724 = [0, 161089812544, 370150799127, 253940052179, 98650531244, 8752647282, 0, 0] := by
  decide +kernel

theorem rows5725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5725 = true := by
  decide +kernel

theorem tot5725 : totK PD2M8K2 D2M8K2.t5725 = [0, 172062817013, 449130944428, 244081554513, 18072998159, 0, 0, 0] := by
  decide +kernel

theorem rows5726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5726 = true := by
  decide +kernel

theorem tot5726 : totK PD2M8K2 D2M8K2.t5726 = [0, 85785976425, 372815399059, 355149754700, 69166773182, 1369150432, 0, 0] := by
  decide +kernel

theorem rows5727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5727 = true := by
  decide +kernel

theorem tot5727 : totK PD2M8K2 D2M8K2.t5727 = [0, 0, 305544626463, 508915430566, 76339538115, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
