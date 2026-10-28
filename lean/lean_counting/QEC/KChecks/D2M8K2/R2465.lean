import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9860 = true := by
  decide +kernel

theorem tot9860 : totK PD2M8K2 D2M8K2.t9860 = [0, 88847742953, 386594793355, 404934029616, 46655047385, 0, 0, 0] := by
  decide +kernel

theorem rows9861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9861 = true := by
  decide +kernel

theorem tot9861 : totK PD2M8K2 D2M8K2.t9861 = [0, 152812125346, 456941769414, 278041554592, 20857950819, 0, 0, 0] := by
  decide +kernel

theorem rows9862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9862 = true := by
  decide +kernel

theorem tot9862 : totK PD2M8K2 D2M8K2.t9862 = [0, 87996589950, 340274643986, 345804887150, 133521281515, 9977052014, 0, 0] := by
  decide +kernel

theorem rows9863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9863 = true := by
  decide +kernel

theorem tot9863 : totK PD2M8K2 D2M8K2.t9863 = [0, 0, 227098184296, 495443051942, 178662274614, 5133479850, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
