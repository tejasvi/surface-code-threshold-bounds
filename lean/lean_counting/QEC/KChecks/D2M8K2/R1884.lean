import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7536 = true := by
  decide +kernel

theorem tot7536 : totK PD2M8K2 D2M8K2.t7536 = [0, 0, 154592944783, 452292659779, 283567495725, 26423188598, 0, 0] := by
  decide +kernel

theorem rows7537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7537 = true := by
  decide +kernel

theorem tot7537 : totK PD2M8K2 D2M8K2.t7537 = [0, 0, 187420295940, 454168469695, 230588194142, 14030657234, 0, 0] := by
  decide +kernel

theorem rows7538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7538 = true := by
  decide +kernel

theorem tot7538 : totK PD2M8K2 D2M8K2.t7538 = [0, 0, 168908814071, 437688285315, 275846229622, 30067917985, 0, 0] := by
  decide +kernel

theorem rows7539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7539 = true := by
  decide +kernel

theorem tot7539 : totK PD2M8K2 D2M8K2.t7539 = [0, 0, 137743620891, 456184753336, 273554569945, 12243590021, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
