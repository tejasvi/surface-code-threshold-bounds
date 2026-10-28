import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6492 = true := by
  decide +kernel

theorem tot6492 : totK PD2M8K2 D2M8K2.t6492 = [0, 136647621132, 447359749762, 304025853024, 31051892900, 0, 0, 0] := by
  decide +kernel

theorem rows6493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6493 = true := by
  decide +kernel

theorem tot6493 : totK PD2M8K2 D2M8K2.t6493 = [0, 0, 176914168813, 445083757522, 250381158545, 25191558099, 0, 0] := by
  decide +kernel

theorem rows6494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6494 = true := by
  decide +kernel

theorem tot6494 : totK PD2M8K2 D2M8K2.t6494 = [0, 0, 198494436727, 503363985225, 183763915632, 5206224793, 0, 0] := by
  decide +kernel

theorem rows6495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6495 = true := by
  decide +kernel

theorem tot6495 : totK PD2M8K2 D2M8K2.t6495 = [0, 157176254258, 387146580814, 257930983653, 91945969766, 6524090962, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
