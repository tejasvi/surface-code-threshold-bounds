import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9104 = true := by
  decide +kernel

theorem tot9104 : totK PD2M8K2 D2M8K2.t9104 = [0, 92925902623, 380794211619, 395069236890, 49763613827, 0, 0, 0] := by
  decide +kernel

theorem rows9105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9105 = true := by
  decide +kernel

theorem tot9105 : totK PD2M8K2 D2M8K2.t9105 = [0, 166040761728, 449261214022, 260662278132, 21438651677, 0, 0, 0] := by
  decide +kernel

theorem rows9106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9106 = true := by
  decide +kernel

theorem tot9106 : totK PD2M8K2 D2M8K2.t9106 = [0, 158470454872, 456606112518, 276830749822, 29089212004, 0, 0, 0] := by
  decide +kernel

theorem rows9107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9107 = true := by
  decide +kernel

theorem tot9107 : totK PD2M8K2 D2M8K2.t9107 = [0, 0, 217631393639, 482914373712, 197334084635, 12531227089, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
