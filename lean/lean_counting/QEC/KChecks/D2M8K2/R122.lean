import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t488 = true := by
  decide +kernel

theorem tot488 : totK PD2M8K2 D2M8K2.t488 = [0, 0, 191507671029, 481119455176, 214614920034, 6476941105, 0, 0] := by
  decide +kernel

theorem rows489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t489 = true := by
  decide +kernel

theorem tot489 : totK PD2M8K2 D2M8K2.t489 = [0, 160916176433, 362455369805, 263833602210, 105634297576, 6761253570, 0, 0] := by
  decide +kernel

theorem rows490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t490 = true := by
  decide +kernel

theorem tot490 : totK PD2M8K2 D2M8K2.t490 = [0, 158411176553, 439979770461, 285540415605, 30356596475, 0, 0, 0] := by
  decide +kernel

theorem rows491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t491 = true := by
  decide +kernel

theorem tot491 : totK PD2M8K2 D2M8K2.t491 = [0, 105786884607, 426922503787, 330241468832, 30686462885, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
