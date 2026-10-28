import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13780 = true := by
  decide +kernel

theorem tot13780 : totK PD2M8K2 D2M8K2.t13780 = [65755919475, 242214751303, 397515620591, 183680491040, 8214505460, 0, 0, 0] := by
  decide +kernel

theorem rows13781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13781 = true := by
  decide +kernel

theorem tot13781 : totK PD2M8K2 D2M8K2.t13781 = [182676119445, 470821950107, 257100798772, 23187703520, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13782 = true := by
  decide +kernel

theorem tot13782 : totK PD2M8K2 D2M8K2.t13782 = [171674375026, 457910438293, 242583139887, 14841966833, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13783 = true := by
  decide +kernel

theorem tot13783 : totK PD2M8K2 D2M8K2.t13783 = [0, 265174122483, 507146220146, 123973147837, 2287653690, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
