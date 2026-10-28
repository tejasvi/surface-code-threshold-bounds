import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2928 = true := by
  decide +kernel

theorem tot2928 : totK PD2M8K2 D2M8K2.t2928 = [0, 174583700023, 466790166136, 239013473790, 13673275291, 0, 0, 0] := by
  decide +kernel

theorem rows2929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2929 = true := by
  decide +kernel

theorem tot2929 : totK PD2M8K2 D2M8K2.t2929 = [0, 0, 289470310960, 464549144481, 94152910956, 1095107716, 0, 0] := by
  decide +kernel

theorem rows2930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2930 = true := by
  decide +kernel

theorem tot2930 : totK PD2M8K2 D2M8K2.t2930 = [105517004570, 236727843737, 187402556625, 246237970882, 92815941467, 3882006667, 0, 0] := by
  decide +kernel

theorem rows2931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2931 = true := by
  decide +kernel

theorem tot2931 : totK PD2M8K2 D2M8K2.t2931 = [185044739640, 468094246300, 226188159840, 15536972036, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
