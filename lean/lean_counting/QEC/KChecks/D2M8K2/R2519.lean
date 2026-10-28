import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10076 = true := by
  decide +kernel

theorem tot10076 : totK PD2M8K2 D2M8K2.t10076 = [0, 0, 203149397750, 473021902852, 213244106017, 13264216520, 0, 0] := by
  decide +kernel

theorem rows10077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10077 = true := by
  decide +kernel

theorem tot10077 : totK PD2M8K2 D2M8K2.t10077 = [0, 0, 169199132608, 454959615785, 270621384630, 28746623399, 0, 0] := by
  decide +kernel

theorem rows10078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10078 = true := by
  decide +kernel

theorem tot10078 : totK PD2M8K2 D2M8K2.t10078 = [0, 0, 188384696397, 491379224566, 218242184360, 6701235243, 0, 0] := by
  decide +kernel

theorem rows10079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10079 = true := by
  decide +kernel

theorem tot10079 : totK PD2M8K2 D2M8K2.t10079 = [0, 0, 160809153057, 453780889954, 268297075165, 23080048912, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
