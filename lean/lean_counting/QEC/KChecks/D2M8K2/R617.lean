import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2468 = true := by
  decide +kernel

theorem tot2468 : totK PD2M8K2 D2M8K2.t2468 = [0, 172446104734, 459690545743, 247145418762, 16221412778, 0, 0, 0] := by
  decide +kernel

theorem rows2469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2469 = true := by
  decide +kernel

theorem tot2469 : totK PD2M8K2 D2M8K2.t2469 = [0, 0, 276130252626, 479852443422, 128912662576, 4031931762, 0, 0] := by
  decide +kernel

theorem rows2470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2470 = true := by
  decide +kernel

theorem tot2470 : totK PD2M8K2 D2M8K2.t2470 = [0, 85096583084, 337538508749, 376586882208, 82151967427, 1186940923, 0, 0] := by
  decide +kernel

theorem rows2471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2471 = true := by
  decide +kernel

theorem tot2471 : totK PD2M8K2 D2M8K2.t2471 = [0, 168763094863, 436456353315, 275598491747, 30307792245, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
