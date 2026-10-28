import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10752 = true := by
  decide +kernel

theorem tot10752 : totK PD2M8K2 D2M8K2.t10752 = [0, 0, 174646411684, 437833669825, 246874897019, 42405719869, 2569691499, 0] := by
  decide +kernel

theorem rows10753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10753 = true := by
  decide +kernel

theorem tot10753 : totK PD2M8K2 D2M8K2.t10753 = [0, 0, 174368692269, 437223742850, 267009044317, 26587087494, 0, 0] := by
  decide +kernel

theorem rows10754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10754 = true := by
  decide +kernel

theorem tot10754 : totK PD2M8K2 D2M8K2.t10754 = [0, 0, 92932490688, 400701317014, 345887814685, 51231783722, 1096505104, 0] := by
  decide +kernel

theorem rows10755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10755 = true := by
  decide +kernel

theorem tot10755 : totK PD2M8K2 D2M8K2.t10755 = [0, 0, 0, 314067222164, 520213530803, 80506279559, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
