import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10024 = true := by
  decide +kernel

theorem tot10024 : totK PD2M8K2 D2M8K2.t10024 = [0, 181695580645, 453316332936, 270419784470, 27900272367, 0, 0, 0] := by
  decide +kernel

theorem rows10025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10025 = true := by
  decide +kernel

theorem tot10025 : totK PD2M8K2 D2M8K2.t10025 = [0, 171140408864, 458028819935, 248155484989, 13024479281, 0, 0, 0] := by
  decide +kernel

theorem rows10026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10026 = true := by
  decide +kernel

theorem tot10026 : totK PD2M8K2 D2M8K2.t10026 = [0, 0, 230717558336, 496116023932, 161665187507, 6821150176, 0, 0] := by
  decide +kernel

theorem rows10027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10027 = true := by
  decide +kernel

theorem tot10027 : totK PD2M8K2 D2M8K2.t10027 = [0, 67565028568, 317354155215, 391229574744, 97989997354, 2266161007, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
