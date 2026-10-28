import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8908 = true := by
  decide +kernel

theorem tot8908 : totK PD2M8K2 D2M8K2.t8908 = [171580439313, 461931901182, 248132793784, 17534395127, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8909 = true := by
  decide +kernel

theorem tot8909 : totK PD2M8K2 D2M8K2.t8909 = [0, 276710476589, 507833697284, 108429609869, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows8910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8910 = true := by
  decide +kernel

theorem tot8910 : totK PD2M8K2 D2M8K2.t8910 = [108504643250, 378979374878, 382516895839, 53070135962, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8911 = true := by
  decide +kernel

theorem tot8911 : totK PD2M8K2 D2M8K2.t8911 = [192155251367, 478867839718, 226768101522, 14042036721, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
