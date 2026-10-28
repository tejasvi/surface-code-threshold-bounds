import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10768 = true := by
  decide +kernel

theorem tot10768 : totK PD2M8K2 D2M8K2.t10768 = [0, 92089433884, 164272448925, 48458575347, 163249103501, 318744042507, 93467172928, 3882006667] := by
  decide +kernel

theorem rows10769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10769 = true := by
  decide +kernel

theorem tot10769 : totK PD2M8K2 D2M8K2.t10769 = [0, 171807008291, 469864995753, 234787476769, 14566626306, 0, 0, 0] := by
  decide +kernel

theorem rows10770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10770 = true := by
  decide +kernel

theorem tot10770 : totK PD2M8K2 D2M8K2.t10770 = [0, 169597878671, 463125960909, 244056631751, 13019437864, 0, 0, 0] := by
  decide +kernel

theorem rows10771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10771 = true := by
  decide +kernel

theorem tot10771 : totK PD2M8K2 D2M8K2.t10771 = [0, 0, 271800512341, 509226217342, 114548461905, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
