import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2304 = true := by
  decide +kernel

theorem tot2304 : totK PD2M8K2 D2M8K2.t2304 = [0, 0, 203194132828, 478120138527, 208143775107, 7994456143, 0, 0] := by
  decide +kernel

theorem rows2305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2305 = true := by
  decide +kernel

theorem tot2305 : totK PD2M8K2 D2M8K2.t2305 = [0, 67372906060, 252897919066, 391260890297, 176938615859, 8214505460, 0, 0] := by
  decide +kernel

theorem rows2306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2306 = true := by
  decide +kernel

theorem tot2306 : totK PD2M8K2 D2M8K2.t2306 = [0, 180199927621, 453505140507, 262688603691, 27928042127, 0, 0, 0] := by
  decide +kernel

theorem rows2307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2307 = true := by
  decide +kernel

theorem tot2307 : totK PD2M8K2 D2M8K2.t2307 = [0, 155963652404, 456844600655, 268888283804, 20049256354, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
