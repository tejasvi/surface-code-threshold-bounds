import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3468 = true := by
  decide +kernel

theorem tot3468 : totK PD2M8K2 D2M8K2.t3468 = [0, 173459609035, 474480285172, 257846475208, 14209021188, 0, 0, 0] := by
  decide +kernel

theorem rows3469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3469 = true := by
  decide +kernel

theorem tot3469 : totK PD2M8K2 D2M8K2.t3469 = [0, 0, 278973939999, 501043411943, 121372144293, 1238673482, 0, 0] := by
  decide +kernel

theorem rows3470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3470 = true := by
  decide +kernel

theorem tot3470 : totK PD2M8K2 D2M8K2.t3470 = [87370076960, 145997249234, 134413103556, 341269866386, 160725350238, 8063697217, 0, 0] := by
  decide +kernel

theorem rows3471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3471 = true := by
  decide +kernel

theorem tot3471 : totK PD2M8K2 D2M8K2.t3471 = [157356916162, 447570483601, 254986606536, 18481811774, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
