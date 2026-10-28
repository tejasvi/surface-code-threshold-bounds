import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2268 = true := by
  decide +kernel

theorem tot2268 : totK PD2M8K2 D2M8K2.t2268 = [0, 0, 0, 307459532054, 475374321902, 92812463579, 1067409660, 0] := by
  decide +kernel

theorem rows2269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2269 = true := by
  decide +kernel

theorem tot2269 : totK PD2M8K2 D2M8K2.t2269 = [0, 179096909081, 451273943074, 197007215003, 41165244839, 32046384099, 2814597007, 0] := by
  decide +kernel

theorem rows2270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2270 = true := by
  decide +kernel

theorem tot2270 : totK PD2M8K2 D2M8K2.t2270 = [0, 202804401331, 470180151573, 213553507565, 12534051746, 0, 0, 0] := by
  decide +kernel

theorem rows2271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2271 = true := by
  decide +kernel

theorem tot2271 : totK PD2M8K2 D2M8K2.t2271 = [0, 55608356038, 332444981000, 423342605421, 92758688011, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
