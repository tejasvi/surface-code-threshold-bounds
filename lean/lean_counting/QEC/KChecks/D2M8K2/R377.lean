import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1508 = true := by
  decide +kernel

theorem tot1508 : totK PD2M8K2 D2M8K2.t1508 = [0, 176314638416, 447835232562, 252178666186, 23717821541, 0, 0, 0] := by
  decide +kernel

theorem rows1509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1509 = true := by
  decide +kernel

theorem tot1509 : totK PD2M8K2 D2M8K2.t1509 = [0, 102379680894, 424294783466, 341929930963, 30742448113, 0, 0, 0] := by
  decide +kernel

theorem rows1510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1510 = true := by
  decide +kernel

theorem tot1510 : totK PD2M8K2 D2M8K2.t1510 = [0, 0, 210283066489, 479398233430, 179084989937, 9587713104, 0, 0] := by
  decide +kernel

theorem rows1511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1511 = true := by
  decide +kernel

theorem tot1511 : totK PD2M8K2 D2M8K2.t1511 = [0, 87978670910, 341739029916, 361035044089, 91680799295, 3462014130, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
