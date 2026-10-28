import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7248 = true := by
  decide +kernel

theorem tot7248 : totK PD2M8K2 D2M8K2.t7248 = [0, 0, 179722208364, 454634998367, 259650002133, 21035774224, 0, 0] := by
  decide +kernel

theorem rows7249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7249 = true := by
  decide +kernel

theorem tot7249 : totK PD2M8K2 D2M8K2.t7249 = [0, 0, 87132176421, 378545361784, 365578671738, 58713717273, 1164319620, 0] := by
  decide +kernel

theorem rows7250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7250 = true := by
  decide +kernel

theorem tot7250 : totK PD2M8K2 D2M8K2.t7250 = [0, 0, 0, 242957703788, 493997939454, 154301451226, 8423393484, 0] := by
  decide +kernel

theorem rows7251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7251 = true := by
  decide +kernel

theorem tot7251 : totK PD2M8K2 D2M8K2.t7251 = [0, 0, 103791020940, 346962017652, 340987129058, 83744139876, 3462014130, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
