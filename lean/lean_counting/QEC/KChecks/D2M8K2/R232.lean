import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t928 = true := by
  decide +kernel

theorem tot928 : totK PD2M8K2 D2M8K2.t928 = [0, 206776383460, 481205266569, 201630198453, 7994456143, 0, 0, 0] := by
  decide +kernel

theorem rows929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t929 = true := by
  decide +kernel

theorem tot929 : totK PD2M8K2 D2M8K2.t929 = [86906743190, 269039111821, 361823832537, 174828437061, 8214505460, 0, 0, 0] := by
  decide +kernel

theorem rows930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t930 = true := by
  decide +kernel

theorem tot930 : totK PD2M8K2 D2M8K2.t930 = [167687891573, 436528505805, 278508963069, 30394842057, 0, 0, 0, 0] := by
  decide +kernel

theorem rows931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t931 = true := by
  decide +kernel

theorem tot931 : totK PD2M8K2 D2M8K2.t931 = [147810817928, 446568544234, 280831184180, 22080179390, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
