import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15336 = true := by
  decide +kernel

theorem tot15336 : totK PD2M8K2 D2M8K2.t15336 = [0, 0, 242411395903, 497986295872, 154464176049, 7143121018, 0, 0] := by
  decide +kernel

theorem rows15337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15337 = true := by
  decide +kernel

theorem tot15337 : totK PD2M8K2 D2M8K2.t15337 = [0, 65835198230, 283729051258, 393312440480, 123814083365, 4476305813, 0, 0] := by
  decide +kernel

theorem rows15338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15338 = true := by
  decide +kernel

theorem tot15338 : totK PD2M8K2 D2M8K2.t15338 = [0, 182755202180, 459207357682, 263086463650, 24549257228, 0, 0, 0] := by
  decide +kernel

theorem rows15339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15339 = true := by
  decide +kernel

theorem tot15339 : totK PD2M8K2 D2M8K2.t15339 = [0, 171745346510, 466940011040, 241384927624, 12275853398, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
