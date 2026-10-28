import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3676 = true := by
  decide +kernel

theorem tot3676 : totK PD2M8K2 D2M8K2.t3676 = [0, 56111990362, 347605296055, 416980504545, 79278014178, 1096505104, 0, 0] := by
  decide +kernel

theorem rows3677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3677 = true := by
  decide +kernel

theorem tot3677 : totK PD2M8K2 D2M8K2.t3677 = [0, 0, 271599183469, 514417676750, 114999450669, 2158098333, 0, 0] := by
  decide +kernel

theorem rows3678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3678 = true := by
  decide +kernel

theorem tot3678 : totK PD2M8K2 D2M8K2.t3678 = [0, 0, 203040363837, 465474024635, 181242484887, 11360414200, 0, 0] := by
  decide +kernel

theorem rows3679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3679 = true := by
  decide +kernel

theorem tot3679 : totK PD2M8K2 D2M8K2.t3679 = [0, 0, 186603981463, 467866913646, 194805261355, 12316110946, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
