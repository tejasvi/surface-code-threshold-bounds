import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t344 = true := by
  decide +kernel

theorem tot344 : totK PD2M8K2 D2M8K2.t344 = [0, 157007335367, 400247359189, 282896354556, 72324066503, 1415142070, 0, 0] := by
  decide +kernel

theorem rows345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t345 = true := by
  decide +kernel

theorem tot345 : totK PD2M8K2 D2M8K2.t345 = [0, 192140106604, 462235007733, 236855258899, 16553905388, 0, 0, 0] := by
  decide +kernel

theorem rows346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t346 = true := by
  decide +kernel

theorem tot346 : totK PD2M8K2 D2M8K2.t346 = [0, 52289221100, 394544453366, 403470018179, 56399554119, 0, 0, 0] := by
  decide +kernel

theorem rows347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t347 = true := by
  decide +kernel

theorem tot347 : totK PD2M8K2 D2M8K2.t347 = [0, 0, 179069359629, 497586919462, 191131128155, 3622693787, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
