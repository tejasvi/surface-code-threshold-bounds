import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11948 = true := by
  decide +kernel

theorem tot11948 : totK PD2M8K2 D2M8K2.t11948 = [125022379307, 453151535513, 301489312979, 23596080815, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11949 = true := by
  decide +kernel

theorem tot11949 : totK PD2M8K2 D2M8K2.t11949 = [0, 284914805025, 523807928829, 100675420909, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows11950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11950 = true := by
  decide +kernel

theorem tot11950 : totK PD2M8K2 D2M8K2.t11950 = [137424393192, 356747556729, 288864210114, 90172558489, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows11951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11951 = true := by
  decide +kernel

theorem tot11951 : totK PD2M8K2 D2M8K2.t11951 = [175061402411, 452224539795, 262368136821, 23874494047, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
