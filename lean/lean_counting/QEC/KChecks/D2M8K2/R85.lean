import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t340 = true := by
  decide +kernel

theorem tot340 : totK PD2M8K2 D2M8K2.t340 = [0, 100465153446, 338304564712, 365461754940, 79222622276, 1149959346, 0, 0] := by
  decide +kernel

theorem rows341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t341 = true := by
  decide +kernel

theorem tot341 : totK PD2M8K2 D2M8K2.t341 = [0, 168496674639, 436676960821, 271420972726, 30233651744, 0, 0, 0] := by
  decide +kernel

theorem rows342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t342 = true := by
  decide +kernel

theorem tot342 : totK PD2M8K2 D2M8K2.t342 = [0, 130262121946, 441559863882, 294504000769, 17111936285, 0, 0, 0] := by
  decide +kernel

theorem rows343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t343 = true := by
  decide +kernel

theorem tot343 : totK PD2M8K2 D2M8K2.t343 = [0, 0, 320118392204, 513771809599, 76886641921, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
