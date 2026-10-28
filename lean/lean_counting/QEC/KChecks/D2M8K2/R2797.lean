import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11188 = true := by
  decide +kernel

theorem tot11188 : totK PD2M8K2 D2M8K2.t11188 = [0, 0, 255909401115, 491985317531, 139060598040, 8357116046, 0, 0] := by
  decide +kernel

theorem rows11189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11189 = true := by
  decide +kernel

theorem tot11189 : totK PD2M8K2 D2M8K2.t11189 = [0, 153980021500, 388911080284, 269930028599, 64614726310, 3462014130, 0, 0] := by
  decide +kernel

theorem rows11190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11190 = true := by
  decide +kernel

theorem tot11190 : totK PD2M8K2 D2M8K2.t11190 = [0, 167611746817, 442343864082, 272900225376, 28304733758, 0, 0, 0] := by
  decide +kernel

theorem rows11191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11191 = true := by
  decide +kernel

theorem tot11191 : totK PD2M8K2 D2M8K2.t11191 = [0, 82104992921, 370792291695, 356081886908, 63910170059, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
