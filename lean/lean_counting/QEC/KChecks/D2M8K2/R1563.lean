import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6252 = true := by
  decide +kernel

theorem tot6252 : totK PD2M8K2 D2M8K2.t6252 = [0, 194222928427, 443026152667, 212302961225, 16891742343, 0, 0, 0] := by
  decide +kernel

theorem rows6253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6253 = true := by
  decide +kernel

theorem tot6253 : totK PD2M8K2 D2M8K2.t6253 = [0, 120914751584, 436771303834, 287726684037, 21496292155, 0, 0, 0] := by
  decide +kernel

theorem rows6254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6254 = true := by
  decide +kernel

theorem tot6254 : totK PD2M8K2 D2M8K2.t6254 = [0, 22679135244, 336180406945, 433911965611, 69306397324, 1138244013, 0, 0] := by
  decide +kernel

theorem rows6255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6255 = true := by
  decide +kernel

theorem tot6255 : totK PD2M8K2 D2M8K2.t6255 = [0, 171688517969, 445992718511, 261434578555, 29170585304, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
