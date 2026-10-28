import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15704 = true := by
  decide +kernel

theorem tot15704 : totK PD2M8K2 D2M8K2.t15704 = [0, 0, 88995923185, 321821909592, 374421260333, 136090315839, 8758169719, 0] := by
  decide +kernel

theorem rows15705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15705 = true := by
  decide +kernel

theorem tot15705 : totK PD2M8K2 D2M8K2.t15705 = [0, 0, 0, 304812802221, 479741300663, 130685255380, 3306524588, 0] := by
  decide +kernel

theorem rows15706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15706 = true := by
  decide +kernel

theorem tot15706 : totK PD2M8K2 D2M8K2.t15706 = [0, 0, 160149215015, 376888183194, 272947720301, 95708876549, 4246544562, 0] := by
  decide +kernel

theorem rows15707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15707 = true := by
  decide +kernel

theorem tot15707 : totK PD2M8K2 D2M8K2.t15707 = [0, 0, 175416715011, 444479182246, 263566051346, 20831450554, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
