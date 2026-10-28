import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8876 = true := by
  decide +kernel

theorem tot8876 : totK PD2M8K2 D2M8K2.t8876 = [173439528345, 468589965035, 247319125815, 13739823492, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8877 = true := by
  decide +kernel

theorem tot8877 : totK PD2M8K2 D2M8K2.t8877 = [0, 295963706617, 499977902706, 112364156573, 1197396724, 0, 0, 0] := by
  decide +kernel

theorem rows8878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8878 = true := by
  decide +kernel

theorem tot8878 : totK PD2M8K2 D2M8K2.t8878 = [0, 191195101457, 474536294139, 194883430959, 12040273252, 0, 0, 0] := by
  decide +kernel

theorem rows8879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8879 = true := by
  decide +kernel

theorem tot8879 : totK PD2M8K2 D2M8K2.t8879 = [193690295225, 451888845141, 243530536292, 26190348010, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
