import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4916 = true := by
  decide +kernel

theorem tot4916 : totK PD2M8K2 D2M8K2.t4916 = [0, 0, 67906090413, 93559942698, 245918884272, 371035490535, 76525408679, 1430229726] := by
  decide +kernel

theorem rows4917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4917 = true := by
  decide +kernel

theorem tot4917 : totK PD2M8K2 D2M8K2.t4917 = [0, 0, 221449614133, 485026405064, 192821009188, 6677095838, 0, 0] := by
  decide +kernel

theorem rows4918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4918 = true := by
  decide +kernel

theorem tot4918 : totK PD2M8K2 D2M8K2.t4918 = [0, 0, 87961091318, 347918514634, 375101446583, 75597608673, 1369150432, 0] := by
  decide +kernel

theorem rows4919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4919 = true := by
  decide +kernel

theorem tot4919 : totK PD2M8K2 D2M8K2.t4919 = [0, 0, 76919059275, 382189319367, 407628709397, 46094706162, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
