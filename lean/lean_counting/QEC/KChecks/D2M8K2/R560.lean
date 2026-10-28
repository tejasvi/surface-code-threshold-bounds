import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2240 = true := by
  decide +kernel

theorem tot2240 : totK PD2M8K2 D2M8K2.t2240 = [0, 52730177238, 302744624884, 370163593208, 159750626229, 16756554836, 0, 0] := by
  decide +kernel

theorem rows2241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2241 = true := by
  decide +kernel

theorem tot2241 : totK PD2M8K2 D2M8K2.t2241 = [0, 0, 204698061879, 464803313090, 201420779134, 10198636971, 0, 0] := by
  decide +kernel

theorem rows2242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2242 = true := by
  decide +kernel

theorem tot2242 : totK PD2M8K2 D2M8K2.t2242 = [0, 84647800555, 267676662921, 370715476878, 157925962379, 3782038083, 0, 0] := by
  decide +kernel

theorem rows2243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2243 = true := by
  decide +kernel

theorem tot2243 : totK PD2M8K2 D2M8K2.t2243 = [0, 177896681605, 458011073670, 246808786923, 22288945394, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
