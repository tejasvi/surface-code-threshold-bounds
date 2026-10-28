import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9720 = true := by
  decide +kernel

theorem tot9720 : totK PD2M8K2 D2M8K2.t9720 = [0, 0, 0, 305062433403, 449776860341, 108573413207, 4028038878, 0] := by
  decide +kernel

theorem rows9721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9721 = true := by
  decide +kernel

theorem tot9721 : totK PD2M8K2 D2M8K2.t9721 = [0, 0, 267494808591, 467594774388, 143496811372, 9682236039, 0, 0] := by
  decide +kernel

theorem rows9722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9722 = true := by
  decide +kernel

theorem tot9722 : totK PD2M8K2 D2M8K2.t9722 = [0, 0, 206975305808, 491000497687, 171573239153, 5179312808, 0, 0] := by
  decide +kernel

theorem rows9723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9723 = true := by
  decide +kernel

theorem tot9723 : totK PD2M8K2 D2M8K2.t9723 = [0, 0, 186430398076, 463514469987, 228907748158, 15065290503, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
