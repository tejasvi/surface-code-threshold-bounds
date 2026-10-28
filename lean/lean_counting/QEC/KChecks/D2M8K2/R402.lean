import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1608 = true := by
  decide +kernel

theorem tot1608 : totK PD2M8K2 D2M8K2.t1608 = [0, 137922024301, 433885572580, 299032295647, 28497402597, 0, 0, 0] := by
  decide +kernel

theorem rows1609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1609 = true := by
  decide +kernel

theorem tot1609 : totK PD2M8K2 D2M8K2.t1609 = [0, 0, 273247422518, 507782097582, 110422196374, 1369150432, 0, 0] := by
  decide +kernel

theorem rows1610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1610 = true := by
  decide +kernel

theorem tot1610 : totK PD2M8K2 D2M8K2.t1610 = [0, 155674148643, 449679089911, 284260998016, 20822689268, 0, 0, 0] := by
  decide +kernel

theorem rows1611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1611 = true := by
  decide +kernel

theorem tot1611 : totK PD2M8K2 D2M8K2.t1611 = [0, 170422407598, 465710333349, 233923203344, 16811237680, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
