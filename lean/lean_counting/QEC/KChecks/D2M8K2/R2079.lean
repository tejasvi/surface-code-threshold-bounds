import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8316 = true := by
  decide +kernel

theorem tot8316 : totK PD2M8K2 D2M8K2.t8316 = [178733406942, 446864766655, 240000083298, 17115888737, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8317 = true := by
  decide +kernel

theorem tot8317 : totK PD2M8K2 D2M8K2.t8317 = [118542424389, 422796660951, 314915658029, 31255505530, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8318 = true := by
  decide +kernel

theorem tot8318 : totK PD2M8K2 D2M8K2.t8318 = [0, 275912574443, 504725069967, 110530796890, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows8319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8319 = true := by
  decide +kernel

theorem tot8319 : totK PD2M8K2 D2M8K2.t8319 = [157202694930, 417595425699, 309536970363, 37330961240, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
