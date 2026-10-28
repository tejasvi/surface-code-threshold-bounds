import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4052 = true := by
  decide +kernel

theorem tot4052 : totK PD2M8K2 D2M8K2.t4052 = [0, 0, 0, 327766337266, 517303208415, 70564824815, 0, 0] := by
  decide +kernel

theorem rows4053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4053 = true := by
  decide +kernel

theorem tot4053 : totK PD2M8K2 D2M8K2.t4053 = [0, 0, 157758791320, 395213449716, 290176911150, 74018155246, 1415142070, 0] := by
  decide +kernel

theorem rows4054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4054 = true := by
  decide +kernel

theorem tot4054 : totK PD2M8K2 D2M8K2.t4054 = [0, 0, 173130873977, 456550796021, 253490174593, 17270753052, 0, 0] := by
  decide +kernel

theorem rows4055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4055 = true := by
  decide +kernel

theorem tot4055 : totK PD2M8K2 D2M8K2.t4055 = [0, 0, 89002152038, 423960403124, 360694849815, 40499773758, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
