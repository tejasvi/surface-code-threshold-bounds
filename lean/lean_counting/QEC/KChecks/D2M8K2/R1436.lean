import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5744 = true := by
  decide +kernel

theorem tot5744 : totK PD2M8K2 D2M8K2.t5744 = [0, 152273806677, 433006965594, 293224760616, 31496266548, 0, 0, 0] := by
  decide +kernel

theorem rows5745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5745 = true := by
  decide +kernel

theorem tot5745 : totK PD2M8K2 D2M8K2.t5745 = [0, 87996001221, 408945643029, 373936640054, 47186882241, 0, 0, 0] := by
  decide +kernel

theorem rows5746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5746 = true := by
  decide +kernel

theorem tot5746 : totK PD2M8K2 D2M8K2.t5746 = [0, 84834164928, 318676418848, 396869774075, 97883610927, 1409560813, 0, 0] := by
  decide +kernel

theorem rows5747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5747 = true := by
  decide +kernel

theorem tot5747 : totK PD2M8K2 D2M8K2.t5747 = [0, 171425265570, 460947377813, 259016441589, 20884263647, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
