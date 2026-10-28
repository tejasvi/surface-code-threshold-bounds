import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9512 = true := by
  decide +kernel

theorem tot9512 : totK PD2M8K2 D2M8K2.t9512 = [153381683531, 445870558319, 273392664107, 21692205094, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9513 = true := by
  decide +kernel

theorem tot9513 : totK PD2M8K2 D2M8K2.t9513 = [0, 269620181546, 490398140244, 115312545669, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows9514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9514 = true := by
  decide +kernel

theorem tot9514 : totK PD2M8K2 D2M8K2.t9514 = [147857160341, 408557891525, 333624851003, 42423810293, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9515 = true := by
  decide +kernel

theorem tot9515 : totK PD2M8K2 D2M8K2.t9515 = [171800671615, 484520011264, 243179337795, 14475470953, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
