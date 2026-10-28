import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8992 = true := by
  decide +kernel

theorem tot8992 : totK PD2M8K2 D2M8K2.t8992 = [36252083209, 219979686211, 433051486695, 188960236618, 12045711471, 0, 0, 0] := by
  decide +kernel

theorem rows8993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8993 = true := by
  decide +kernel

theorem tot8993 : totK PD2M8K2 D2M8K2.t8993 = [187287733965, 461648988821, 252633508223, 23003889729, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8994 = true := by
  decide +kernel

theorem tot8994 : totK PD2M8K2 D2M8K2.t8994 = [191616693984, 472364922429, 231487758128, 14769520758, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8995 = true := by
  decide +kernel

theorem tot8995 : totK PD2M8K2 D2M8K2.t8995 = [23758972037, 312827861503, 462387327090, 102493915736, 1268739303, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
