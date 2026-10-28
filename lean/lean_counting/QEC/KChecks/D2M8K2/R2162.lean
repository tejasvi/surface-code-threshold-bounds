import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8648 = true := by
  decide +kernel

theorem tot8648 : totK PD2M8K2 D2M8K2.t8648 = [0, 203986543884, 485466755513, 183177037312, 7442000727, 0, 0, 0] := by
  decide +kernel

theorem rows8649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8649 = true := by
  decide +kernel

theorem tot8649 : totK PD2M8K2 D2M8K2.t8649 = [0, 157982198884, 464870328492, 244993853854, 15859045170, 0, 0, 0] := by
  decide +kernel

theorem rows8650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8650 = true := by
  decide +kernel

theorem tot8650 : totK PD2M8K2 D2M8K2.t8650 = [0, 171799827768, 469658220718, 253068486864, 13239322405, 0, 0, 0] := by
  decide +kernel

theorem rows8651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8651 = true := by
  decide +kernel

theorem tot8651 : totK PD2M8K2 D2M8K2.t8651 = [0, 0, 278446126673, 504746006280, 97085979397, 1310285577, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
