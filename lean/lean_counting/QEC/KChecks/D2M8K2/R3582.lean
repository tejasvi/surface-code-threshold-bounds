import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14328 = true := by
  decide +kernel

theorem tot14328 : totK PD2M8K2 D2M8K2.t14328 = [0, 196743109617, 460975861274, 241118545594, 23353249267, 2174602308, 0, 0] := by
  decide +kernel

theorem rows14329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14329 = true := by
  decide +kernel

theorem tot14329 : totK PD2M8K2 D2M8K2.t14329 = [0, 193867550929, 461554639437, 221416529714, 12313560678, 0, 0, 0] := by
  decide +kernel

theorem rows14330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14330 = true := by
  decide +kernel

theorem tot14330 : totK PD2M8K2 D2M8K2.t14330 = [0, 33688335845, 372697706301, 448128161176, 62775040480, 0, 0, 0] := by
  decide +kernel

theorem rows14331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14331 = true := by
  decide +kernel

theorem tot14331 : totK PD2M8K2 D2M8K2.t14331 = [0, 0, 206589445123, 472534722122, 182078788955, 11873025674, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
