import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16276 = true := by
  decide +kernel

theorem tot16276 : totK PD2M8K2 D2M8K2.t16276 = [0, 0, 168892681230, 441360643253, 282783065683, 28501372804, 0, 0] := by
  decide +kernel

theorem rows16277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16277 = true := by
  decide +kernel

theorem tot16277 : totK PD2M8K2 D2M8K2.t16277 = [0, 0, 87922896509, 434200587144, 353080201364, 40252960643, 0, 0] := by
  decide +kernel

theorem rows16278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16278 = true := by
  decide +kernel

theorem tot16278 : totK PD2M8K2 D2M8K2.t16278 = [0, 0, 0, 288927229025, 488969484574, 121656980934, 4189012250, 0] := by
  decide +kernel

theorem rows16279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16279 = true := by
  decide +kernel

theorem tot16279 : totK PD2M8K2 D2M8K2.t16279 = [0, 0, 192437972909, 460500869136, 251645332568, 31013471590, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
