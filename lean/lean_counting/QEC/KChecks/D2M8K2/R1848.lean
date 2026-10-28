import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7392 = true := by
  decide +kernel

theorem tot7392 : totK PD2M8K2 D2M8K2.t7392 = [0, 178668588682, 452602377728, 264457859255, 27411793113, 0, 0, 0] := by
  decide +kernel

theorem rows7393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7393 = true := by
  decide +kernel

theorem tot7393 : totK PD2M8K2 D2M8K2.t7393 = [0, 155906640865, 450219627865, 280280451932, 23464239892, 0, 0, 0] := by
  decide +kernel

theorem rows7394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7394 = true := by
  decide +kernel

theorem tot7394 : totK PD2M8K2 D2M8K2.t7394 = [0, 0, 242730500386, 498519349020, 152675741300, 2659251643, 0, 0] := by
  decide +kernel

theorem rows7395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7395 = true := by
  decide +kernel

theorem tot7395 : totK PD2M8K2 D2M8K2.t7395 = [0, 0, 181530813022, 459888861493, 230264353532, 15642982414, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
