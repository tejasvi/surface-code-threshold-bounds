import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14532 = true := by
  decide +kernel

theorem tot14532 : totK PD2M8K2 D2M8K2.t14532 = [89266124844, 233611923520, 336015836938, 231008468613, 22079973395, 0, 0, 0] := by
  decide +kernel

theorem rows14533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14533 = true := by
  decide +kernel

theorem tot14533 : totK PD2M8K2 D2M8K2.t14533 = [152989216845, 457249135240, 252901772956, 16961991347, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14534 = true := by
  decide +kernel

theorem tot14534 : totK PD2M8K2 D2M8K2.t14534 = [153142458884, 442325701201, 269644408451, 20449372323, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14535 = true := by
  decide +kernel

theorem tot14535 : totK PD2M8K2 D2M8K2.t14535 = [0, 270357765306, 498029210649, 112081700911, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
