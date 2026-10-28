import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6504 = true := by
  decide +kernel

theorem tot6504 : totK PD2M8K2 D2M8K2.t6504 = [0, 175803011529, 473749639326, 232996074688, 12454572399, 0, 0, 0] := by
  decide +kernel

theorem rows6505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6505 = true := by
  decide +kernel

theorem tot6505 : totK PD2M8K2 D2M8K2.t6505 = [0, 0, 324830635526, 516156248423, 61398684842, 0, 0, 0] := by
  decide +kernel

theorem rows6506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6506 = true := by
  decide +kernel

theorem tot6506 : totK PD2M8K2 D2M8K2.t6506 = [0, 122493971330, 339312946680, 364746173473, 97193438419, 1415142070, 0, 0] := by
  decide +kernel

theorem rows6507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6507 = true := by
  decide +kernel

theorem tot6507 : totK PD2M8K2 D2M8K2.t6507 = [0, 205521119295, 476477949283, 224470092649, 12119513722, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
