import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2676 = true := by
  decide +kernel

theorem tot2676 : totK PD2M8K2 D2M8K2.t2676 = [0, 0, 277196668235, 514697644356, 112679819963, 1069412848, 0, 0] := by
  decide +kernel

theorem rows2677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2677 = true := by
  decide +kernel

theorem tot2677 : totK PD2M8K2 D2M8K2.t2677 = [0, 183090000448, 442938512342, 238575432047, 35337616759, 2814597007, 0, 0] := by
  decide +kernel

theorem rows2678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2678 = true := by
  decide +kernel

theorem tot2678 : totK PD2M8K2 D2M8K2.t2678 = [0, 203234606008, 477828917742, 222552386652, 13824426958, 0, 0, 0] := by
  decide +kernel

theorem rows2679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2679 = true := by
  decide +kernel

theorem tot2679 : totK PD2M8K2 D2M8K2.t2679 = [0, 25977005429, 310587430616, 450385200297, 97378948185, 1232398321, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
