import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11952 = true := by
  decide +kernel

theorem tot11952 : totK PD2M8K2 D2M8K2.t11952 = [91570829045, 370649937486, 364157061162, 65276578693, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows11953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11953 = true := by
  decide +kernel

theorem tot11953 : totK PD2M8K2 D2M8K2.t11953 = [0, 227556145854, 497835740110, 157904982679, 2099832254, 0, 0, 0] := by
  decide +kernel

theorem rows11954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11954 = true := by
  decide +kernel

theorem tot11954 : totK PD2M8K2 D2M8K2.t11954 = [0, 181262983847, 459481585091, 225578825519, 17276947703, 0, 0, 0] := by
  decide +kernel

theorem rows11955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11955 = true := by
  decide +kernel

theorem tot11955 : totK PD2M8K2 D2M8K2.t11955 = [0, 194109308072, 471882155702, 203611638043, 9713690252, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
