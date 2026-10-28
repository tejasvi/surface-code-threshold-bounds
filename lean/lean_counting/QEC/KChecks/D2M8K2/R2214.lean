import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8856 = true := by
  decide +kernel

theorem tot8856 : totK PD2M8K2 D2M8K2.t8856 = [0, 155510060804, 457148013034, 249691732813, 18471174381, 0, 0, 0] := by
  decide +kernel

theorem rows8857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8857 = true := by
  decide +kernel

theorem tot8857 : totK PD2M8K2 D2M8K2.t8857 = [0, 0, 285684220359, 457911040583, 106685806223, 1369150432, 0, 0] := by
  decide +kernel

theorem rows8858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8858 = true := by
  decide +kernel

theorem tot8858 : totK PD2M8K2 D2M8K2.t8858 = [0, 157887881646, 445825405989, 257024140539, 22695287968, 0, 0, 0] := by
  decide +kernel

theorem rows8859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8859 = true := by
  decide +kernel

theorem tot8859 : totK PD2M8K2 D2M8K2.t8859 = [0, 162967371074, 440995616652, 245667099798, 16087094179, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
