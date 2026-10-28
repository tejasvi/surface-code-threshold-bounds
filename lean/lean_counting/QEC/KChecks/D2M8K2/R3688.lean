import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14752 = true := by
  decide +kernel

theorem tot14752 : totK PD2M8K2 D2M8K2.t14752 = [0, 63011064965, 333904527637, 389689506131, 90542728512, 1369150432, 0, 0] := by
  decide +kernel

theorem rows14753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14753 = true := by
  decide +kernel

theorem tot14753 : totK PD2M8K2 D2M8K2.t14753 = [0, 55038698513, 362677862554, 392056145777, 52125744069, 0, 0, 0] := by
  decide +kernel

theorem rows14754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14754 = true := by
  decide +kernel

theorem tot14754 : totK PD2M8K2 D2M8K2.t14754 = [0, 189551043462, 489961763342, 215481500489, 6473261923, 0, 0, 0] := by
  decide +kernel

theorem rows14755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14755 = true := by
  decide +kernel

theorem tot14755 : totK PD2M8K2 D2M8K2.t14755 = [0, 163339893011, 451969408976, 240984400153, 14936878817, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
