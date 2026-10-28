import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14228 = true := by
  decide +kernel

theorem tot14228 : totK PD2M8K2 D2M8K2.t14228 = [165526147959, 358380080007, 240542729788, 127302505810, 13554132542, 0, 0, 0] := by
  decide +kernel

theorem rows14229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14229 = true := by
  decide +kernel

theorem tot14229 : totK PD2M8K2 D2M8K2.t14229 = [158800436828, 445274135730, 249589770541, 18197172049, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14230 = true := by
  decide +kernel

theorem tot14230 : totK PD2M8K2 D2M8K2.t14230 = [67142989855, 322819633725, 387495367088, 92581978797, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows14231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14231 = true := by
  decide +kernel

theorem tot14231 : totK PD2M8K2 D2M8K2.t14231 = [38447064568, 343953821342, 465331120119, 59293416695, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
