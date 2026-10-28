import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15060 = true := by
  decide +kernel

theorem tot15060 : totK PD2M8K2 D2M8K2.t15060 = [0, 0, 109974802622, 399618103393, 313043525392, 45792335778, 1086231185, 0] := by
  decide +kernel

theorem rows15061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15061 = true := by
  decide +kernel

theorem tot15061 : totK PD2M8K2 D2M8K2.t15061 = [0, 0, 0, 275958512624, 447884155053, 112150670879, 3752012233, 0] := by
  decide +kernel

theorem rows15062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15062 = true := by
  decide +kernel

theorem tot15062 : totK PD2M8K2 D2M8K2.t15062 = [0, 0, 174952877924, 459980286796, 253078837864, 25128242702, 0, 0] := by
  decide +kernel

theorem rows15063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15063 = true := by
  decide +kernel

theorem tot15063 : totK PD2M8K2 D2M8K2.t15063 = [0, 0, 174159052329, 454117407630, 243884797738, 16882332783, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
