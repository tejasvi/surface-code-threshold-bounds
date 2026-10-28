import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1500 = true := by
  decide +kernel

theorem tot1500 : totK PD2M8K2 D2M8K2.t1500 = [0, 0, 174159052329, 455230851298, 247913421458, 16882332783, 0, 0] := by
  decide +kernel

theorem rows1501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1501 = true := by
  decide +kernel

theorem tot1501 : totK PD2M8K2 D2M8K2.t1501 = [0, 0, 89878208072, 343763912657, 373284223373, 85144512607, 1242138600, 0] := by
  decide +kernel

theorem rows1502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1502 = true := by
  decide +kernel

theorem tot1502 : totK PD2M8K2 D2M8K2.t1502 = [0, 0, 0, 237250097262, 466659269791, 149712808749, 5613010732, 0] := by
  decide +kernel

theorem rows1503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1503 = true := by
  decide +kernel

theorem tot1503 : totK PD2M8K2 D2M8K2.t1503 = [0, 92342479873, 218915502108, 166703770704, 257693695028, 145773606145, 13326740810, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
