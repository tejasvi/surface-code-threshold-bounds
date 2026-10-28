import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11032 = true := by
  decide +kernel

theorem tot11032 : totK PD2M8K2 D2M8K2.t11032 = [0, 177570949089, 443600418736, 279773082715, 32911276479, 0, 0, 0] := by
  decide +kernel

theorem rows11033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11033 = true := by
  decide +kernel

theorem tot11033 : totK PD2M8K2 D2M8K2.t11033 = [0, 195480876546, 468077434805, 225547719532, 15594018672, 0, 0, 0] := by
  decide +kernel

theorem rows11034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11034 = true := by
  decide +kernel

theorem tot11034 : totK PD2M8K2 D2M8K2.t11034 = [0, 183522642543, 465781419456, 241605004459, 19790844544, 0, 0, 0] := by
  decide +kernel

theorem rows11035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11035 = true := by
  decide +kernel

theorem tot11035 : totK PD2M8K2 D2M8K2.t11035 = [0, 189549014987, 468696596076, 218848823260, 12439805748, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
