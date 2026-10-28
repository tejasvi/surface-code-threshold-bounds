import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10228 = true := by
  decide +kernel

theorem tot10228 : totK PD2M8K2 D2M8K2.t10228 = [0, 109118455231, 316373670492, 365140802386, 135343940615, 6804944647, 0, 0] := by
  decide +kernel

theorem rows10229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10229 = true := by
  decide +kernel

theorem tot10229 : totK PD2M8K2 D2M8K2.t10229 = [0, 211699485731, 491495980725, 196929003668, 7269569142, 0, 0, 0] := by
  decide +kernel

theorem rows10230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10230 = true := by
  decide +kernel

theorem tot10230 : totK PD2M8K2 D2M8K2.t10230 = [0, 4187750769, 300247371664, 484670534853, 123288450004, 4441674612, 0, 0] := by
  decide +kernel

theorem rows10231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10231 = true := by
  decide +kernel

theorem tot10231 : totK PD2M8K2 D2M8K2.t10231 = [0, 98948767120, 352906129346, 365902897563, 77765741871, 2468388885, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
