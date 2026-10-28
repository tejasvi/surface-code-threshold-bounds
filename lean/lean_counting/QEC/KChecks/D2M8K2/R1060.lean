import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4240 = true := by
  decide +kernel

theorem tot4240 : totK PD2M8K2 D2M8K2.t4240 = [0, 0, 93572267332, 390502494618, 387069184073, 51680741930, 0, 0] := by
  decide +kernel

theorem rows4241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4241 = true := by
  decide +kernel

theorem tot4241 : totK PD2M8K2 D2M8K2.t4241 = [0, 0, 162746285713, 448552674855, 282653731690, 24163057242, 0, 0] := by
  decide +kernel

theorem rows4242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4242 = true := by
  decide +kernel

theorem tot4242 : totK PD2M8K2 D2M8K2.t4242 = [0, 0, 174692607031, 467221551105, 240939497535, 11455643192, 0, 0] := by
  decide +kernel

theorem rows4243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4243 = true := by
  decide +kernel

theorem tot4243 : totK PD2M8K2 D2M8K2.t4243 = [0, 0, 0, 186721911760, 462862333804, 244109612775, 24256071441, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
