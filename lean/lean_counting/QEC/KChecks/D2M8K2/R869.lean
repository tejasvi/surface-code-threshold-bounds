import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3476 = true := by
  decide +kernel

theorem tot3476 : totK PD2M8K2 D2M8K2.t3476 = [70684700304, 294178543948, 363532598241, 175472299344, 19376420146, 0, 0, 0] := by
  decide +kernel

theorem rows3477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3477 = true := by
  decide +kernel

theorem tot3477 : totK PD2M8K2 D2M8K2.t3477 = [0, 212154138791, 483109065534, 208050716149, 7992090037, 0, 0, 0] := by
  decide +kernel

theorem rows3478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3478 = true := by
  decide +kernel

theorem tot3478 : totK PD2M8K2 D2M8K2.t3478 = [84066023774, 254533467903, 371814670245, 177093970097, 8188124600, 0, 0, 0] := by
  decide +kernel

theorem rows3479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3479 = true := by
  decide +kernel

theorem tot3479 : totK PD2M8K2 D2M8K2.t3479 = [182382651690, 463831912229, 254732217633, 23071260255, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
