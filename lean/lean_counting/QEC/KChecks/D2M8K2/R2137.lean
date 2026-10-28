import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8548 = true := by
  decide +kernel

theorem tot8548 : totK PD2M8K2 D2M8K2.t8548 = [0, 163845717703, 427872871488, 289962114809, 35251483856, 0, 0, 0] := by
  decide +kernel

theorem rows8549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8549 = true := by
  decide +kernel

theorem tot8549 : totK PD2M8K2 D2M8K2.t8549 = [0, 198463881715, 480690208992, 215501874296, 11405872210, 0, 0, 0] := by
  decide +kernel

theorem rows8550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8550 = true := by
  decide +kernel

theorem tot8550 : totK PD2M8K2 D2M8K2.t8550 = [0, 170294058138, 467716196679, 240490030819, 15490801784, 0, 0, 0] := by
  decide +kernel

theorem rows8551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8551 = true := by
  decide +kernel

theorem tot8551 : totK PD2M8K2 D2M8K2.t8551 = [0, 182197762482, 477360901374, 246776500552, 17149033700, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
