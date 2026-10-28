import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7340 = true := by
  decide +kernel

theorem tot7340 : totK PD2M8K2 D2M8K2.t7340 = [0, 0, 66215051750, 311963888884, 423387541965, 95608944460, 1415142070, 0] := by
  decide +kernel

theorem rows7341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7341 = true := by
  decide +kernel

theorem tot7341 : totK PD2M8K2 D2M8K2.t7341 = [0, 0, 177071376237, 455873478660, 262360546704, 24230767999, 0, 0] := by
  decide +kernel

theorem rows7342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7342 = true := by
  decide +kernel

theorem tot7342 : totK PD2M8K2 D2M8K2.t7342 = [0, 0, 177626494765, 472704334256, 244144920059, 12085319996, 0, 0] := by
  decide +kernel

theorem rows7343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7343 = true := by
  decide +kernel

theorem tot7343 : totK PD2M8K2 D2M8K2.t7343 = [0, 0, 0, 298173031006, 485172582491, 107437099970, 1238673482, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
