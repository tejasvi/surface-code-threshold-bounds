import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3044 = true := by
  decide +kernel

theorem tot3044 : totK PD2M8K2 D2M8K2.t3044 = [0, 0, 154179626819, 454431022009, 232503554047, 14446206483, 0, 0] := by
  decide +kernel

theorem rows3045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3045 = true := by
  decide +kernel

theorem tot3045 : totK PD2M8K2 D2M8K2.t3045 = [0, 0, 0, 299895245299, 441149086116, 74709795687, 1021600638, 0] := by
  decide +kernel

theorem rows3046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3046 = true := by
  decide +kernel

theorem tot3046 : totK PD2M8K2 D2M8K2.t3046 = [0, 0, 168522691040, 371243667531, 235876099560, 66409211403, 3552795014, 0] := by
  decide +kernel

theorem rows3047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3047 = true := by
  decide +kernel

theorem tot3047 : totK PD2M8K2 D2M8K2.t3047 = [0, 0, 190505968338, 470426330549, 226856224155, 14517393958, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
