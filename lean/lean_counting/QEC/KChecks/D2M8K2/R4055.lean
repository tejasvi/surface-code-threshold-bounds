import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16220 = true := by
  decide +kernel

theorem tot16220 : totK PD2M8K2 D2M8K2.t16220 = [0, 0, 164078816122, 461569111159, 229235582524, 9064506700, 0, 0] := by
  decide +kernel

theorem rows16221 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16221 = true := by
  decide +kernel

theorem tot16221 : totK PD2M8K2 D2M8K2.t16221 = [0, 0, 75296688379, 342014125669, 393669953881, 78381506730, 1310285577, 0] := by
  decide +kernel

theorem rows16222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16222 = true := by
  decide +kernel

theorem tot16222 : totK PD2M8K2 D2M8K2.t16222 = [0, 0, 49307896513, 352928133525, 451611481666, 43756317456, 0, 0] := by
  decide +kernel

theorem rows16223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16223 = true := by
  decide +kernel

theorem tot16223 : totK PD2M8K2 D2M8K2.t16223 = [0, 0, 163654933336, 441818533137, 277486393143, 27953710199, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
