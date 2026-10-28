import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13672 = true := by
  decide +kernel

theorem tot13672 : totK PD2M8K2 D2M8K2.t13672 = [0, 173536382757, 469257879674, 233945826619, 15850701526, 0, 0, 0] := by
  decide +kernel

theorem rows13673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13673 = true := by
  decide +kernel

theorem tot13673 : totK PD2M8K2 D2M8K2.t13673 = [0, 88237066013, 335931954740, 384595572617, 91308781315, 1369150432, 0, 0] := by
  decide +kernel

theorem rows13674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13674 = true := by
  decide +kernel

theorem tot13674 : totK PD2M8K2 D2M8K2.t13674 = [0, 0, 335005565688, 512395505640, 61949129390, 0, 0, 0] := by
  decide +kernel

theorem rows13675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13675 = true := by
  decide +kernel

theorem tot13675 : totK PD2M8K2 D2M8K2.t13675 = [0, 209216869345, 459536309826, 218156047197, 17153985407, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
