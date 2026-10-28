import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2352 = true := by
  decide +kernel

theorem tot2352 : totK PD2M8K2 D2M8K2.t2352 = [0, 0, 195922672640, 479137911499, 197150321475, 6239403452, 0, 0] := by
  decide +kernel

theorem rows2353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2353 = true := by
  decide +kernel

theorem tot2353 : totK PD2M8K2 D2M8K2.t2353 = [0, 0, 0, 307748033007, 464636369234, 80001133700, 1206465782, 0] := by
  decide +kernel

theorem rows2354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2354 = true := by
  decide +kernel

theorem tot2354 : totK PD2M8K2 D2M8K2.t2354 = [0, 0, 124846214789, 415933216175, 329076911134, 37124542456, 0, 0] := by
  decide +kernel

theorem rows2355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2355 = true := by
  decide +kernel

theorem tot2355 : totK PD2M8K2 D2M8K2.t2355 = [0, 0, 174817928095, 486151235784, 230924990110, 11565565407, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
