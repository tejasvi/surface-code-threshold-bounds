import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14588 = true := by
  decide +kernel

theorem tot14588 : totK PD2M8K2 D2M8K2.t14588 = [0, 89267215531, 386590753371, 362444201056, 53474537579, 1075657031, 0, 0] := by
  decide +kernel

theorem rows14589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14589 = true := by
  decide +kernel

theorem tot14589 : totK PD2M8K2 D2M8K2.t14589 = [0, 7167183939, 257044531725, 496063088888, 128313724919, 3804183361, 0, 0] := by
  decide +kernel

theorem rows14590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14590 = true := by
  decide +kernel

theorem tot14590 : totK PD2M8K2 D2M8K2.t14590 = [0, 182995280951, 460743885087, 239211404882, 20859769259, 0, 0, 0] := by
  decide +kernel

theorem rows14591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14591 = true := by
  decide +kernel

theorem tot14591 : totK PD2M8K2 D2M8K2.t14591 = [0, 203683608962, 469664318265, 212971327572, 12233076403, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
