import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15832 = true := by
  decide +kernel

theorem tot15832 : totK PD2M8K2 D2M8K2.t15832 = [0, 0, 178231051108, 447178654827, 277364779241, 30284134194, 0, 0] := by
  decide +kernel

theorem rows15833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15833 = true := by
  decide +kernel

theorem tot15833 : totK PD2M8K2 D2M8K2.t15833 = [0, 0, 203655890553, 481882301693, 217904877355, 8977779328, 0, 0] := by
  decide +kernel

theorem rows15834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15834 = true := by
  decide +kernel

theorem tot15834 : totK PD2M8K2 D2M8K2.t15834 = [0, 0, 59649953388, 291305762231, 374023497022, 172224892502, 17884690775, 0] := by
  decide +kernel

theorem rows15835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15835 = true := by
  decide +kernel

theorem tot15835 : totK PD2M8K2 D2M8K2.t15835 = [0, 0, 0, 222534637110, 487644434684, 177589297407, 5323774734, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
