import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9152 = true := by
  decide +kernel

theorem tot9152 : totK PD2M8K2 D2M8K2.t9152 = [112590929234, 262567162580, 162197080655, 225214866179, 132698247117, 13338039113, 0, 0] := by
  decide +kernel

theorem rows9153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9153 = true := by
  decide +kernel

theorem tot9153 : totK PD2M8K2 D2M8K2.t9153 = [179308174545, 455300623591, 236944330362, 17115888737, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9154 = true := by
  decide +kernel

theorem tot9154 : totK PD2M8K2 D2M8K2.t9154 = [137144555594, 439685929850, 290680839399, 24941489021, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9155 = true := by
  decide +kernel

theorem tot9155 : totK PD2M8K2 D2M8K2.t9155 = [0, 273017084381, 510200011524, 110363347364, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
