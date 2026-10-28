import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16120 = true := by
  decide +kernel

theorem tot16120 : totK PD2M8K2 D2M8K2.t16120 = [0, 0, 0, 336686558556, 487913627655, 77091398097, 0, 0] := by
  decide +kernel

theorem rows16121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16121 = true := by
  decide +kernel

theorem tot16121 : totK PD2M8K2 D2M8K2.t16121 = [0, 0, 89427196855, 308276281257, 392905942812, 108229320708, 2681443193, 0] := by
  decide +kernel

theorem rows16122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16122 = true := by
  decide +kernel

theorem tot16122 : totK PD2M8K2 D2M8K2.t16122 = [0, 0, 164199702955, 433823314718, 277933663689, 28918587728, 0, 0] := by
  decide +kernel

theorem rows16123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16123 = true := by
  decide +kernel

theorem tot16123 : totK PD2M8K2 D2M8K2.t16123 = [0, 0, 72705645835, 412627646639, 394794307781, 43716566980, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
