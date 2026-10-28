import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2520 = true := by
  decide +kernel

theorem tot2520 : totK PD2M8K2 D2M8K2.t2520 = [0, 211463872857, 497925616533, 195386550252, 5430665091, 0, 0, 0] := by
  decide +kernel

theorem rows2521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2521 = true := by
  decide +kernel

theorem tot2521 : totK PD2M8K2 D2M8K2.t2521 = [171607033725, 367889084397, 254308132822, 103537886079, 6799735859, 0, 0, 0] := by
  decide +kernel

theorem rows2522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2522 = true := by
  decide +kernel

theorem tot2522 : totK PD2M8K2 D2M8K2.t2522 = [161392857845, 445788154282, 287013496123, 30437197709, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2523 = true := by
  decide +kernel

theorem tot2523 : totK PD2M8K2 D2M8K2.t2523 = [107275408861, 429873599581, 335511664983, 28640706407, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
