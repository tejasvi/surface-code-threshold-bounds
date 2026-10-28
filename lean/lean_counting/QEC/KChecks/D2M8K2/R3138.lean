import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12552 = true := by
  decide +kernel

theorem tot12552 : totK PD2M8K2 D2M8K2.t12552 = [0, 0, 217163309291, 500615947767, 169685722803, 4970660381, 0, 0] := by
  decide +kernel

theorem rows12553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12553 = true := by
  decide +kernel

theorem tot12553 : totK PD2M8K2 D2M8K2.t12553 = [0, 0, 204985867467, 480657607523, 191561082141, 9262708636, 0, 0] := by
  decide +kernel

theorem rows12554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12554 = true := by
  decide +kernel

theorem tot12554 : totK PD2M8K2 D2M8K2.t12554 = [0, 0, 189039127114, 459467986662, 207196013759, 12361325328, 0, 0] := by
  decide +kernel

theorem rows12555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12555 = true := by
  decide +kernel

theorem tot12555 : totK PD2M8K2 D2M8K2.t12555 = [0, 0, 19348689120, 320716525276, 432330072672, 75380383864, 1239866073, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
