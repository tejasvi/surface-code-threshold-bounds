import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2260 = true := by
  decide +kernel

theorem tot2260 : totK PD2M8K2 D2M8K2.t2260 = [0, 0, 191808196098, 504687232409, 189569555328, 4081155540, 0, 0] := by
  decide +kernel

theorem rows2261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2261 = true := by
  decide +kernel

theorem tot2261 : totK PD2M8K2 D2M8K2.t2261 = [0, 0, 177590752180, 460093345544, 238804775849, 16776741768, 0, 0] := by
  decide +kernel

theorem rows2262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2262 = true := by
  decide +kernel

theorem tot2262 : totK PD2M8K2 D2M8K2.t2262 = [0, 0, 204508134374, 469792162605, 194377141867, 9120623527, 0, 0] := by
  decide +kernel

theorem rows2263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2263 = true := by
  decide +kernel

theorem tot2263 : totK PD2M8K2 D2M8K2.t2263 = [0, 0, 193841141121, 479955006718, 209267153564, 11066126582, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
