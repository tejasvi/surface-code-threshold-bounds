import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3996 = true := by
  decide +kernel

theorem tot3996 : totK PD2M8K2 D2M8K2.t3996 = [0, 0, 279259051533, 504787056400, 121925039672, 1268739303, 0, 0] := by
  decide +kernel

theorem rows3997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3997 = true := by
  decide +kernel

theorem tot3997 : totK PD2M8K2 D2M8K2.t3997 = [0, 0, 181152648832, 484235482450, 210336496624, 8669917095, 0, 0] := by
  decide +kernel

theorem rows3998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3998 = true := by
  decide +kernel

theorem tot3998 : totK PD2M8K2 D2M8K2.t3998 = [0, 0, 172095978565, 463908197351, 219757839788, 14631128802, 0, 0] := by
  decide +kernel

theorem rows3999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3999 = true := by
  decide +kernel

theorem tot3999 : totK PD2M8K2 D2M8K2.t3999 = [0, 0, 201422704211, 464446535917, 176889944811, 6702054242, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
