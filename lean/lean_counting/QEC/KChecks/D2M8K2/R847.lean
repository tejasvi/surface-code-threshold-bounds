import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3388 = true := by
  decide +kernel

theorem tot3388 : totK PD2M8K2 D2M8K2.t3388 = [0, 173680543228, 434840842699, 291909731061, 34689772918, 0, 0, 0] := by
  decide +kernel

theorem rows3389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3389 = true := by
  decide +kernel

theorem tot3389 : totK PD2M8K2 D2M8K2.t3389 = [0, 171972639511, 474264485136, 248140668197, 15678197524, 0, 0, 0] := by
  decide +kernel

theorem rows3390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3390 = true := by
  decide +kernel

theorem tot3390 : totK PD2M8K2 D2M8K2.t3390 = [0, 70862748273, 302112751687, 374537747310, 155038908582, 15179291327, 0, 0] := by
  decide +kernel

theorem rows3391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3391 = true := by
  decide +kernel

theorem tot3391 : totK PD2M8K2 D2M8K2.t3391 = [0, 0, 208334480619, 479318941882, 202339733687, 9547133780, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
