import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7252 = true := by
  decide +kernel

theorem tot7252 : totK PD2M8K2 D2M8K2.t7252 = [0, 0, 183402958790, 449440804633, 255026144816, 22749913351, 0, 0] := by
  decide +kernel

theorem rows7253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7253 = true := by
  decide +kernel

theorem tot7253 : totK PD2M8K2 D2M8K2.t7253 = [0, 0, 120650788071, 422876682058, 299811035141, 21926263449, 0, 0] := by
  decide +kernel

theorem rows7254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7254 = true := by
  decide +kernel

theorem tot7254 : totK PD2M8K2 D2M8K2.t7254 = [0, 0, 0, 286108116042, 506918310267, 88044188465, 1096505104, 0] := by
  decide +kernel

theorem rows7255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7255 = true := by
  decide +kernel

theorem tot7255 : totK PD2M8K2 D2M8K2.t7255 = [0, 0, 165125535034, 392046897926, 260378927930, 69864398959, 3820764243, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
