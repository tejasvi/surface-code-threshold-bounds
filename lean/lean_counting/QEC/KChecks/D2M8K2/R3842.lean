import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15368 = true := by
  decide +kernel

theorem tot15368 : totK PD2M8K2 D2M8K2.t15368 = [0, 0, 71490399974, 410987861322, 386285012907, 52176608252, 0, 0] := by
  decide +kernel

theorem rows15369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15369 = true := by
  decide +kernel

theorem tot15369 : totK PD2M8K2 D2M8K2.t15369 = [0, 0, 0, 212787971788, 507214012275, 154926060153, 2484078857, 0] := by
  decide +kernel

theorem rows15370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15370 = true := by
  decide +kernel

theorem tot15370 : totK PD2M8K2 D2M8K2.t15370 = [0, 173410526788, 405709206565, 157187113386, 69881913498, 78620634454, 6818291842, 0] := by
  decide +kernel

theorem rows15371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15371 = true := by
  decide +kernel

theorem tot15371 : totK PD2M8K2 D2M8K2.t15371 = [0, 151987819073, 443306599978, 280337171319, 22858919496, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
