import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12476 = true := by
  decide +kernel

theorem tot12476 : totK PD2M8K2 D2M8K2.t12476 = [0, 170162356382, 457450216499, 243933761752, 12985369356, 0, 0, 0] := by
  decide +kernel

theorem rows12477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12477 = true := by
  decide +kernel

theorem tot12477 : totK PD2M8K2 D2M8K2.t12477 = [0, 0, 244388641062, 503287620984, 137413348711, 2348440009, 0, 0] := by
  decide +kernel

theorem rows12478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12478 = true := by
  decide +kernel

theorem tot12478 : totK PD2M8K2 D2M8K2.t12478 = [0, 54618809271, 233141608729, 408596575338, 163072656854, 10902245252, 0, 0] := by
  decide +kernel

theorem rows12479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12479 = true := by
  decide +kernel

theorem tot12479 : totK PD2M8K2 D2M8K2.t12479 = [0, 187179087777, 472914714552, 228514348600, 16449313667, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
