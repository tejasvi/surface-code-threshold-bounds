import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3148 = true := by
  decide +kernel

theorem tot3148 : totK PD2M8K2 D2M8K2.t3148 = [0, 0, 175807633316, 449186665827, 254460737712, 25191558099, 0, 0] := by
  decide +kernel

theorem rows3149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3149 = true := by
  decide +kernel

theorem tot3149 : totK PD2M8K2 D2M8K2.t3149 = [0, 0, 217642864488, 492948229338, 179366166991, 5206224793, 0, 0] := by
  decide +kernel

theorem rows3150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3150 = true := by
  decide +kernel

theorem tot3150 : totK PD2M8K2 D2M8K2.t3150 = [0, 138718858349, 330629338558, 331950927730, 116857668828, 6524090962, 0, 0] := by
  decide +kernel

theorem rows3151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3151 = true := by
  decide +kernel

theorem tot3151 : totK PD2M8K2 D2M8K2.t3151 = [0, 191213227845, 480002212641, 219550751247, 12085633962, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
