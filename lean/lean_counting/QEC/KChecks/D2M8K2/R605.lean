import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2420 = true := by
  decide +kernel

theorem tot2420 : totK PD2M8K2 D2M8K2.t2420 = [0, 0, 155013321811, 456151148988, 258495610433, 18804443201, 0, 0] := by
  decide +kernel

theorem rows2421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2421 = true := by
  decide +kernel

theorem tot2421 : totK PD2M8K2 D2M8K2.t2421 = [0, 0, 0, 280077463544, 494359480320, 85087270304, 1310285577, 0] := by
  decide +kernel

theorem rows2422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2422 = true := by
  decide +kernel

theorem tot2422 : totK PD2M8K2 D2M8K2.t2422 = [0, 0, 140399015563, 401432131596, 339172726196, 39455882551, 0, 0] := by
  decide +kernel

theorem rows2423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2423 = true := by
  decide +kernel

theorem tot2423 : totK PD2M8K2 D2M8K2.t2423 = [0, 0, 175587490013, 476757981226, 231728339877, 10545720524, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
