import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t352 = true := by
  decide +kernel

theorem tot352 : totK PD2M8K2 D2M8K2.t352 = [158349550357, 446393414618, 291420602247, 30337698200, 0, 0, 0, 0] := by
  decide +kernel

theorem rows353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t353 = true := by
  decide +kernel

theorem tot353 : totK PD2M8K2 D2M8K2.t353 = [171887086707, 462776037001, 236879850902, 12401500317, 0, 0, 0, 0] := by
  decide +kernel

theorem rows354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t354 = true := by
  decide +kernel

theorem tot354 : totK PD2M8K2 D2M8K2.t354 = [0, 200585117361, 457477400479, 233741436406, 24127981036, 0, 0, 0] := by
  decide +kernel

theorem rows355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t355 = true := by
  decide +kernel

theorem tot355 : totK PD2M8K2 D2M8K2.t355 = [0, 204506831201, 477121601180, 192429991989, 3666033144, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
