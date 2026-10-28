import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5980 = true := by
  decide +kernel

theorem tot5980 : totK PD2M8K2 D2M8K2.t5980 = [0, 0, 191472581666, 437894429675, 232508272189, 46893598180, 4256931014, 0] := by
  decide +kernel

theorem rows5981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5981 = true := by
  decide +kernel

theorem tot5981 : totK PD2M8K2 D2M8K2.t5981 = [0, 0, 189406229771, 472025039096, 215899073220, 9039890340, 0, 0] := by
  decide +kernel

theorem rows5982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5982 = true := by
  decide +kernel

theorem tot5982 : totK PD2M8K2 D2M8K2.t5982 = [0, 0, 31097459297, 376197437911, 442595705153, 49715393263, 0, 0] := by
  decide +kernel

theorem rows5983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5983 = true := by
  decide +kernel

theorem tot5983 : totK PD2M8K2 D2M8K2.t5983 = [0, 0, 50124425543, 238317824603, 423182123243, 138428572365, 5067863418, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
