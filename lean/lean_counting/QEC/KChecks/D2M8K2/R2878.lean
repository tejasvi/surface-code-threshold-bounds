import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11512 = true := by
  decide +kernel

theorem tot11512 : totK PD2M8K2 D2M8K2.t11512 = [0, 161067282137, 397613727931, 268680797989, 66693737688, 2569691499, 0, 0] := by
  decide +kernel

theorem rows11513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11513 = true := by
  decide +kernel

theorem tot11513 : totK PD2M8K2 D2M8K2.t11513 = [0, 168017776578, 441313372364, 277174933017, 30309431601, 0, 0, 0] := by
  decide +kernel

theorem rows11514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11514 = true := by
  decide +kernel

theorem tot11514 : totK PD2M8K2 D2M8K2.t11514 = [0, 106852402812, 428982379333, 327258465581, 28911101867, 0, 0, 0] := by
  decide +kernel

theorem rows11515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11515 = true := by
  decide +kernel

theorem tot11515 : totK PD2M8K2 D2M8K2.t11515 = [0, 0, 298195089161, 520342004046, 97002571643, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
