import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4200 = true := by
  decide +kernel

theorem tot4200 : totK PD2M8K2 D2M8K2.t4200 = [0, 0, 0, 209609460641, 480491391494, 203729387256, 11096987858, 0] := by
  decide +kernel

theorem rows4201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4201 = true := by
  decide +kernel

theorem tot4201 : totK PD2M8K2 D2M8K2.t4201 = [0, 0, 59699811499, 223326307476, 416770166976, 192901826777, 8214505460, 0] := by
  decide +kernel

theorem rows4202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4202 = true := by
  decide +kernel

theorem tot4202 : totK PD2M8K2 D2M8K2.t4202 = [0, 0, 186748362811, 480309369220, 239159033175, 22055373437, 0, 0] := by
  decide +kernel

theorem rows4203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4203 = true := by
  decide +kernel

theorem tot4203 : totK PD2M8K2 D2M8K2.t4203 = [0, 0, 173256469578, 461928144200, 240270107222, 12737226598, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
