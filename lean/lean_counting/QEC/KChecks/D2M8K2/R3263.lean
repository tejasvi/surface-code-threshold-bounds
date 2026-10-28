import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13052 = true := by
  decide +kernel

theorem tot13052 : totK PD2M8K2 D2M8K2.t13052 = [0, 177929683750, 462349580450, 239162615852, 14997341436, 0, 0, 0] := by
  decide +kernel

theorem rows13053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13053 = true := by
  decide +kernel

theorem tot13053 : totK PD2M8K2 D2M8K2.t13053 = [0, 77894530060, 333535902333, 387583616934, 89874184976, 1369150432, 0, 0] := by
  decide +kernel

theorem rows13054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13054 = true := by
  decide +kernel

theorem tot13054 : totK PD2M8K2 D2M8K2.t13054 = [0, 18616785608, 327180400541, 493112211004, 65289659456, 0, 0, 0] := by
  decide +kernel

theorem rows13055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13055 = true := by
  decide +kernel

theorem tot13055 : totK PD2M8K2 D2M8K2.t13055 = [0, 201942168996, 480412878700, 199098946610, 9847636232, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
