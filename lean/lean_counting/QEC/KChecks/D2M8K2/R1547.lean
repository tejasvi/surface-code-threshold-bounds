import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6188 = true := by
  decide +kernel

theorem tot6188 : totK PD2M8K2 D2M8K2.t6188 = [0, 187083518176, 457805590762, 234372794374, 16771351837, 0, 0, 0] := by
  decide +kernel

theorem rows6189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6189 = true := by
  decide +kernel

theorem tot6189 : totK PD2M8K2 D2M8K2.t6189 = [0, 37079896223, 386533857184, 432616742950, 46866276330, 0, 0, 0] := by
  decide +kernel

theorem rows6190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6190 = true := by
  decide +kernel

theorem tot6190 : totK PD2M8K2 D2M8K2.t6190 = [0, 67630797490, 321432244722, 410140732385, 94617694694, 1415142070, 0, 0] := by
  decide +kernel

theorem rows6191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6191 = true := by
  decide +kernel

theorem tot6191 : totK PD2M8K2 D2M8K2.t6191 = [0, 177174997332, 455575435323, 266211027614, 27343338882, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
