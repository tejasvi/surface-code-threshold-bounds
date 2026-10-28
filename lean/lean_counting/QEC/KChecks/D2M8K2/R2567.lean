import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10268 = true := by
  decide +kernel

theorem tot10268 : totK PD2M8K2 D2M8K2.t10268 = [0, 174351684497, 465697620838, 251378040882, 14381150842, 0, 0, 0] := by
  decide +kernel

theorem rows10269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10269 = true := by
  decide +kernel

theorem tot10269 : totK PD2M8K2 D2M8K2.t10269 = [0, 0, 188038355458, 444565697859, 254835436479, 23209944845, 0, 0] := by
  decide +kernel

theorem rows10270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10270 = true := by
  decide +kernel

theorem tot10270 : totK PD2M8K2 D2M8K2.t10270 = [0, 0, 202798967152, 493792478585, 197867840675, 5430665091, 0, 0] := by
  decide +kernel

theorem rows10271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10271 = true := by
  decide +kernel

theorem tot10271 : totK PD2M8K2 D2M8K2.t10271 = [0, 176600050142, 383414915263, 246344831647, 99377440871, 6510828610, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
