import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9496 = true := by
  decide +kernel

theorem tot9496 : totK PD2M8K2 D2M8K2.t9496 = [0, 142123624119, 354032166651, 295788064060, 106888446503, 6524090962, 0, 0] := by
  decide +kernel

theorem rows9497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9497 = true := by
  decide +kernel

theorem tot9497 : totK PD2M8K2 D2M8K2.t9497 = [0, 193495886571, 461069810225, 227493923248, 15488204943, 0, 0, 0] := by
  decide +kernel

theorem rows9498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9498 = true := by
  decide +kernel

theorem tot9498 : totK PD2M8K2 D2M8K2.t9498 = [0, 49031532584, 376831136129, 429765542204, 53626987119, 0, 0, 0] := by
  decide +kernel

theorem rows9499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9499 = true := by
  decide +kernel

theorem tot9499 : totK PD2M8K2 D2M8K2.t9499 = [0, 67714192740, 259334599386, 413792045617, 145646975193, 5159868635, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
