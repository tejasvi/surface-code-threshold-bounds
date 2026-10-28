import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t688 = true := by
  decide +kernel

theorem tot688 : totK PD2M8K2 D2M8K2.t688 = [0, 181529627328, 473143143787, 245447845743, 13637876644, 0, 0, 0] := by
  decide +kernel

theorem rows689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t689 = true := by
  decide +kernel

theorem tot689 : totK PD2M8K2 D2M8K2.t689 = [167897416824, 398433127642, 220248830752, 90399405145, 12293754876, 0, 0, 0] := by
  decide +kernel

theorem rows690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t690 = true := by
  decide +kernel

theorem tot690 : totK PD2M8K2 D2M8K2.t690 = [173896026319, 470594097166, 236710892902, 13271230369, 0, 0, 0, 0] := by
  decide +kernel

theorem rows691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t691 = true := by
  decide +kernel

theorem tot691 : totK PD2M8K2 D2M8K2.t691 = [67837396906, 308289433278, 407029433455, 97837634498, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
