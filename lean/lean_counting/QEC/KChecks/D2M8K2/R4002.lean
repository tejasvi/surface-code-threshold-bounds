import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16008 = true := by
  decide +kernel

theorem tot16008 : totK PD2M8K2 D2M8K2.t16008 = [0, 0, 186930854592, 444515032133, 266066178534, 21171463492, 0, 0] := by
  decide +kernel

theorem rows16009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16009 = true := by
  decide +kernel

theorem tot16009 : totK PD2M8K2 D2M8K2.t16009 = [0, 0, 45469332870, 345116352162, 400621480963, 69053349111, 1096505104, 0] := by
  decide +kernel

theorem rows16010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16010 = true := by
  decide +kernel

theorem tot16010 : totK PD2M8K2 D2M8K2.t16010 = [0, 0, 69402809628, 309445793100, 395198780881, 96019089082, 3884009855, 0] := by
  decide +kernel

theorem rows16011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16011 = true := by
  decide +kernel

theorem tot16011 : totK PD2M8K2 D2M8K2.t16011 = [0, 0, 169844190840, 460122798516, 249473077354, 22517231058, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
