import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9032 = true := by
  decide +kernel

theorem tot9032 : totK PD2M8K2 D2M8K2.t9032 = [0, 0, 261596154427, 492776348991, 135681754030, 3724448267, 0, 0] := by
  decide +kernel

theorem rows9033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9033 = true := by
  decide +kernel

theorem tot9033 : totK PD2M8K2 D2M8K2.t9033 = [0, 0, 198679855035, 482364895536, 195805760299, 10127428633, 0, 0] := by
  decide +kernel

theorem rows9034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9034 = true := by
  decide +kernel

theorem tot9034 : totK PD2M8K2 D2M8K2.t9034 = [0, 0, 206167079386, 464927494498, 182652371450, 9503353481, 0, 0] := by
  decide +kernel

theorem rows9035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9035 = true := by
  decide +kernel

theorem tot9035 : totK PD2M8K2 D2M8K2.t9035 = [0, 0, 86331905088, 401402220282, 317439341451, 50989735085, 1310517177, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
