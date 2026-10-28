import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t140 = true := by
  decide +kernel

theorem tot140 : totK PD2M8K2 D2M8K2.t140 = [74092972634, 366332789860, 428524461093, 54667723291, 0, 0, 0, 0] := by
  decide +kernel

theorem rows141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t141 = true := by
  decide +kernel

theorem tot141 : totK PD2M8K2 D2M8K2.t141 = [165774447181, 439306369572, 269489390499, 29806669870, 0, 0, 0, 0] := by
  decide +kernel

theorem rows142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t142 = true := by
  decide +kernel

theorem tot142 : totK PD2M8K2 D2M8K2.t142 = [89650922373, 373041497502, 363017543606, 85122276973, 10336186099, 0, 0, 0] := by
  decide +kernel

theorem rows143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t143 = true := by
  decide +kernel

theorem tot143 : totK PD2M8K2 D2M8K2.t143 = [0, 165275593735, 444615850888, 252516950919, 17400941425, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
