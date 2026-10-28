import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15296 = true := by
  decide +kernel

theorem tot15296 : totK PD2M8K2 D2M8K2.t15296 = [0, 0, 172197447882, 449278325810, 243816990187, 18197172049, 0, 0] := by
  decide +kernel

theorem rows15297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15297 = true := by
  decide +kernel

theorem tot15297 : totK PD2M8K2 D2M8K2.t15297 = [0, 0, 70705481682, 343634742147, 389216574592, 73247505260, 1369150432, 0] := by
  decide +kernel

theorem rows15298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15298 = true := by
  decide +kernel

theorem tot15298 : totK PD2M8K2 D2M8K2.t15298 = [0, 0, 25423986821, 346170552635, 493699657777, 42130948819, 0, 0] := by
  decide +kernel

theorem rows15299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15299 = true := by
  decide +kernel

theorem tot15299 : totK PD2M8K2 D2M8K2.t15299 = [0, 0, 205054549529, 477398394586, 215925561203, 9932253404, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
