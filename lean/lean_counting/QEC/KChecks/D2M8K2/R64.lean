import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t256 = true := by
  decide +kernel

theorem tot256 : totK PD2M8K2 D2M8K2.t256 = [0, 169461322841, 452001428952, 259730613541, 22063477848, 0, 0, 0] := by
  decide +kernel

theorem rows257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t257 = true := by
  decide +kernel

theorem tot257 : totK PD2M8K2 D2M8K2.t257 = [0, 156047710220, 456169587369, 266287754320, 20294322346, 0, 0, 0] := by
  decide +kernel

theorem rows258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t258 = true := by
  decide +kernel

theorem tot258 : totK PD2M8K2 D2M8K2.t258 = [0, 0, 247384876457, 503507117479, 126083881507, 2348440009, 0, 0] := by
  decide +kernel

theorem rows259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t259 = true := by
  decide +kernel

theorem tot259 : totK PD2M8K2 D2M8K2.t259 = [0, 83616122925, 268962310198, 374923767968, 140936255512, 10835877391, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
