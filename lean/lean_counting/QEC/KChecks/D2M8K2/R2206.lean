import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8824 = true := by
  decide +kernel

theorem tot8824 : totK PD2M8K2 D2M8K2.t8824 = [0, 0, 170933447734, 457153628305, 265632925876, 25032913235, 0, 0] := by
  decide +kernel

theorem rows8825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8825 = true := by
  decide +kernel

theorem tot8825 : totK PD2M8K2 D2M8K2.t8825 = [0, 0, 177412976942, 442569104508, 244449495245, 14792434639, 0, 0] := by
  decide +kernel

theorem rows8826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8826 = true := by
  decide +kernel

theorem tot8826 : totK PD2M8K2 D2M8K2.t8826 = [0, 0, 52814328721, 395885107324, 413692160387, 39170979498, 0, 0] := by
  decide +kernel

theorem rows8827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8827 = true := by
  decide +kernel

theorem tot8827 : totK PD2M8K2 D2M8K2.t8827 = [0, 0, 104986272759, 350633976285, 360651876600, 70989189308, 1323630408, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
