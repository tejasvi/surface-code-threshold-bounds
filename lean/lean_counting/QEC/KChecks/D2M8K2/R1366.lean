import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5464 = true := by
  decide +kernel

theorem tot5464 : totK PD2M8K2 D2M8K2.t5464 = [0, 0, 0, 188800387156, 458359397547, 239162820390, 17202498578, 0] := by
  decide +kernel

theorem rows5465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5465 = true := by
  decide +kernel

theorem tot5465 : totK PD2M8K2 D2M8K2.t5465 = [0, 0, 0, 87939979134, 438619262905, 327096378264, 26482263840, 0] := by
  decide +kernel

theorem rows5466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5466 = true := by
  decide +kernel

theorem tot5466 : totK PD2M8K2 D2M8K2.t5466 = [0, 0, 0, 56476252202, 318617395274, 413155544662, 86168427831, 1510868091] := by
  decide +kernel

theorem rows5467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5467 = true := by
  decide +kernel

theorem tot5467 : totK PD2M8K2 D2M8K2.t5467 = [0, 0, 0, 296864133397, 484211734443, 108104530403, 1430538882, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
