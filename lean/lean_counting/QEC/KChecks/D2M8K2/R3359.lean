import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13436 = true := by
  decide +kernel

theorem tot13436 : totK PD2M8K2 D2M8K2.t13436 = [0, 0, 182990719437, 442784261086, 216755787285, 14927076159, 0, 0] := by
  decide +kernel

theorem rows13437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13437 = true := by
  decide +kernel

theorem tot13437 : totK PD2M8K2 D2M8K2.t13437 = [0, 0, 40506339023, 321207466745, 420620568493, 79750943919, 1310166938, 0] := by
  decide +kernel

theorem rows13438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13438 = true := by
  decide +kernel

theorem tot13438 : totK PD2M8K2 D2M8K2.t13438 = [0, 0, 92375525502, 391230678348, 366716007861, 41296452902, 0, 0] := by
  decide +kernel

theorem rows13439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13439 = true := by
  decide +kernel

theorem tot13439 : totK PD2M8K2 D2M8K2.t13439 = [0, 0, 158080525840, 442221062195, 291340774619, 19917392279, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
