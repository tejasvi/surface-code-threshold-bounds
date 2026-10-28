import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1096 = true := by
  decide +kernel

theorem tot1096 : totK PD2M8K2 D2M8K2.t1096 = [0, 194070369751, 461758014644, 242371455279, 23240954692, 0, 0, 0] := by
  decide +kernel

theorem rows1097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1097 = true := by
  decide +kernel

theorem tot1097 : totK PD2M8K2 D2M8K2.t1097 = [0, 154874260547, 464457864313, 257934042072, 13492396461, 0, 0, 0] := by
  decide +kernel

theorem rows1098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1098 = true := by
  decide +kernel

theorem tot1098 : totK PD2M8K2 D2M8K2.t1098 = [0, 0, 262933845468, 492558373366, 133766478340, 6972471598, 0, 0] := by
  decide +kernel

theorem rows1099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1099 = true := by
  decide +kernel

theorem tot1099 : totK PD2M8K2 D2M8K2.t1099 = [0, 66771363629, 313209862531, 386681557958, 107781266811, 4900554076, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
