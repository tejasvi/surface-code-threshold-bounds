import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10620 = true := by
  decide +kernel

theorem tot10620 : totK PD2M8K2 D2M8K2.t10620 = [0, 0, 171545254961, 474184753690, 242263137766, 13347262352, 0, 0] := by
  decide +kernel

theorem rows10621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10621 = true := by
  decide +kernel

theorem tot10621 : totK PD2M8K2 D2M8K2.t10621 = [0, 0, 0, 279617040695, 494047467972, 106666837342, 1171084559, 0] := by
  decide +kernel

theorem rows10622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10622 = true := by
  decide +kernel

theorem tot10622 : totK PD2M8K2 D2M8K2.t10622 = [0, 0, 41001686444, 220719426883, 401440706077, 175035893712, 11934365838, 0] := by
  decide +kernel

theorem rows10623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10623 = true := by
  decide +kernel

theorem tot10623 : totK PD2M8K2 D2M8K2.t10623 = [0, 0, 200863619208, 477681405326, 212121856774, 11071105621, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
