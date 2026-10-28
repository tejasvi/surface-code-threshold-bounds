import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11348 = true := by
  decide +kernel

theorem tot11348 : totK PD2M8K2 D2M8K2.t11348 = [0, 174456845556, 453792672310, 247766989702, 20349039118, 0, 0, 0] := by
  decide +kernel

theorem rows11349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11349 = true := by
  decide +kernel

theorem tot11349 : totK PD2M8K2 D2M8K2.t11349 = [0, 208489923760, 482413985081, 210193266743, 9788235105, 0, 0, 0] := by
  decide +kernel

theorem rows11350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11350 = true := by
  decide +kernel

theorem tot11350 : totK PD2M8K2 D2M8K2.t11350 = [0, 204535369420, 483437937468, 215510803800, 11051716772, 0, 0, 0] := by
  decide +kernel

theorem rows11351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11351 = true := by
  decide +kernel

theorem tot11351 : totK PD2M8K2 D2M8K2.t11351 = [0, 159515983245, 467392040394, 244228168834, 13489156608, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
