import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10484 = true := by
  decide +kernel

theorem tot10484 : totK PD2M8K2 D2M8K2.t10484 = [0, 0, 55385571167, 339029146647, 410324137234, 79357197694, 1369150432, 0] := by
  decide +kernel

theorem rows10485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10485 = true := by
  decide +kernel

theorem tot10485 : totK PD2M8K2 D2M8K2.t10485 = [0, 0, 92605247982, 370316125105, 404933940815, 44407814947, 0, 0] := by
  decide +kernel

theorem rows10486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10486 = true := by
  decide +kernel

theorem tot10486 : totK PD2M8K2 D2M8K2.t10486 = [0, 0, 165954656024, 466667518549, 267962760017, 24043727263, 0, 0] := by
  decide +kernel

theorem rows10487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10487 = true := by
  decide +kernel

theorem tot10487 : totK PD2M8K2 D2M8K2.t10487 = [0, 0, 158929510343, 468302974837, 275205370438, 19222310236, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
