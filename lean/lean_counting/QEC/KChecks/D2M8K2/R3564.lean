import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14256 = true := by
  decide +kernel

theorem tot14256 : totK PD2M8K2 D2M8K2.t14256 = [176394742691, 404116293645, 146131227985, 92844588991, 70330583114, 3882006667, 0, 0] := by
  decide +kernel

theorem rows14257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14257 = true := by
  decide +kernel

theorem tot14257 : totK PD2M8K2 D2M8K2.t14257 = [168716690965, 438731408815, 241846869805, 19662215170, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14258 = true := by
  decide +kernel

theorem tot14258 : totK PD2M8K2 D2M8K2.t14258 = [59466743499, 332614992786, 416648525510, 92563144548, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows14259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14259 = true := by
  decide +kernel

theorem tot14259 : totK PD2M8K2 D2M8K2.t14259 = [56666157517, 343659189948, 448544261830, 60766928214, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
