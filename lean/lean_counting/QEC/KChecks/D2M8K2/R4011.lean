import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16044 = true := by
  decide +kernel

theorem tot16044 : totK PD2M8K2 D2M8K2.t16044 = [0, 0, 37815634106, 303694936943, 426943727604, 142428283512, 10519103133, 0] := by
  decide +kernel

theorem rows16045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16045 = true := by
  decide +kernel

theorem tot16045 : totK PD2M8K2 D2M8K2.t16045 = [0, 0, 0, 273668543428, 510250336898, 138537371012, 1535615586, 0] := by
  decide +kernel

theorem rows16046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16046 = true := by
  decide +kernel

theorem tot16046 : totK PD2M8K2 D2M8K2.t16046 = [0, 0, 165330704234, 419152970290, 252315461722, 68202375963, 4239164426, 0] := by
  decide +kernel

theorem rows16047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16047 = true := by
  decide +kernel

theorem tot16047 : totK PD2M8K2 D2M8K2.t16047 = [0, 0, 174219728003, 474369554505, 253924453744, 19279202000, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
