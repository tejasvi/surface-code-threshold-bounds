import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1840 = true := by
  decide +kernel

theorem tot1840 : totK PD2M8K2 D2M8K2.t1840 = [0, 44222268919, 345682871902, 460238081732, 60383105171, 0, 0, 0] := by
  decide +kernel

theorem rows1841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1841 = true := by
  decide +kernel

theorem tot1841 : totK PD2M8K2 D2M8K2.t1841 = [0, 165696151142, 441361585671, 282875113884, 30337698200, 0, 0, 0] := by
  decide +kernel

theorem rows1842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1842 = true := by
  decide +kernel

theorem tot1842 : totK PD2M8K2 D2M8K2.t1842 = [0, 189253081574, 485850827300, 205136625422, 7533388022, 0, 0, 0] := by
  decide +kernel

theorem rows1843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1843 = true := by
  decide +kernel

theorem tot1843 : totK PD2M8K2 D2M8K2.t1843 = [0, 0, 233801687390, 454360213382, 199158725542, 19153527009, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
