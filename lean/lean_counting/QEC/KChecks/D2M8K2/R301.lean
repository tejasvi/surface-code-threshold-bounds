import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1204 = true := by
  decide +kernel

theorem tot1204 : totK PD2M8K2 D2M8K2.t1204 = [0, 154866874292, 468608109789, 257887785753, 14304258562, 0, 0, 0] := by
  decide +kernel

theorem rows1205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1205 = true := by
  decide +kernel

theorem tot1205 : totK PD2M8K2 D2M8K2.t1205 = [0, 187315072510, 467025812983, 221211980563, 12319708528, 0, 0, 0] := by
  decide +kernel

theorem rows1206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1206 = true := by
  decide +kernel

theorem tot1206 : totK PD2M8K2 D2M8K2.t1206 = [0, 203684232975, 479329600374, 209242663616, 10178307621, 0, 0, 0] := by
  decide +kernel

theorem rows1207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1207 = true := by
  decide +kernel

theorem tot1207 : totK PD2M8K2 D2M8K2.t1207 = [0, 183440377136, 456645513343, 219793276397, 16861767938, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
