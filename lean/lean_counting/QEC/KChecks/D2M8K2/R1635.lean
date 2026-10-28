import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6540 = true := by
  decide +kernel

theorem tot6540 : totK PD2M8K2 D2M8K2.t6540 = [0, 176249733897, 484889868688, 243041346813, 12206498855, 0, 0, 0] := by
  decide +kernel

theorem rows6541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6541 = true := by
  decide +kernel

theorem tot6541 : totK PD2M8K2 D2M8K2.t6541 = [0, 161798514851, 464064619550, 241804114785, 14812707230, 0, 0, 0] := by
  decide +kernel

theorem rows6542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6542 = true := by
  decide +kernel

theorem tot6542 : totK PD2M8K2 D2M8K2.t6542 = [0, 0, 308635306160, 466077010669, 75030169484, 1021600638, 0, 0] := by
  decide +kernel

theorem rows6543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6543 = true := by
  decide +kernel

theorem tot6543 : totK PD2M8K2 D2M8K2.t6543 = [0, 133190045769, 356699234908, 293350954030, 73628380942, 3552795014, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
