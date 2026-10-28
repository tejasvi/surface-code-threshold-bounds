import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t828 = true := by
  decide +kernel

theorem tot828 : totK PD2M8K2 D2M8K2.t828 = [0, 0, 136703041967, 439138737734, 262220009694, 19867745840, 0, 0] := by
  decide +kernel

theorem rows829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t829 = true := by
  decide +kernel

theorem tot829 : totK PD2M8K2 D2M8K2.t829 = [0, 0, 0, 295261016957, 459561302806, 81414879065, 1217496766, 0] := by
  decide +kernel

theorem rows830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t830 = true := by
  decide +kernel

theorem tot830 : totK PD2M8K2 D2M8K2.t830 = [0, 0, 213954302210, 450545484749, 230167043505, 22811960269, 0, 0] := by
  decide +kernel

theorem rows831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t831 = true := by
  decide +kernel

theorem tot831 : totK PD2M8K2 D2M8K2.t831 = [0, 0, 187742161372, 497699130188, 199155323561, 8031208919, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
