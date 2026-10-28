import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2716 = true := by
  decide +kernel

theorem tot2716 : totK PD2M8K2 D2M8K2.t2716 = [0, 0, 180608868787, 453372352989, 261248023110, 25943224173, 0, 0] := by
  decide +kernel

theorem rows2717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2717 = true := by
  decide +kernel

theorem tot2717 : totK PD2M8K2 D2M8K2.t2717 = [0, 0, 205584250277, 478619558468, 206309468990, 9073524239, 0, 0] := by
  decide +kernel

theorem rows2718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2718 = true := by
  decide +kernel

theorem tot2718 : totK PD2M8K2 D2M8K2.t2718 = [0, 0, 169221652159, 457069607256, 245192658722, 20474874162, 0, 0] := by
  decide +kernel

theorem rows2719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2719 = true := by
  decide +kernel

theorem tot2719 : totK PD2M8K2 D2M8K2.t2719 = [0, 0, 178366826850, 439670729563, 260275024945, 18561568889, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
