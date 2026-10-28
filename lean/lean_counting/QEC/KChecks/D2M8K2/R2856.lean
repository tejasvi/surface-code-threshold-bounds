import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11424 = true := by
  decide +kernel

theorem tot11424 : totK PD2M8K2 D2M8K2.t11424 = [0, 0, 186287625885, 455831378590, 228803323749, 13182661443, 0, 0] := by
  decide +kernel

theorem rows11425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11425 = true := by
  decide +kernel

theorem tot11425 : totK PD2M8K2 D2M8K2.t11425 = [0, 0, 37442279120, 388593005419, 431599588081, 40008926360, 0, 0] := by
  decide +kernel

theorem rows11426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11426 = true := by
  decide +kernel

theorem tot11426 : totK PD2M8K2 D2M8K2.t11426 = [0, 0, 77333528695, 330382028542, 395083053859, 83339718636, 1392055030, 0] := by
  decide +kernel

theorem rows11427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11427 = true := by
  decide +kernel

theorem tot11427 : totK PD2M8K2 D2M8K2.t11427 = [0, 0, 174135556961, 438218376673, 264122766205, 26962658215, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
