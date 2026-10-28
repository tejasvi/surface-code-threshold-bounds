import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13816 = true := by
  decide +kernel

theorem tot13816 : totK PD2M8K2 D2M8K2.t13816 = [0, 0, 231142017796, 503801987607, 147042764976, 2484078857, 0, 0] := by
  decide +kernel

theorem rows13817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13817 = true := by
  decide +kernel

theorem tot13817 : totK PD2M8K2 D2M8K2.t13817 = [138054411630, 292274864948, 151558967894, 195821249478, 108547000558, 6818291842, 0, 0] := by
  decide +kernel

theorem rows13818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13818 = true := by
  decide +kernel

theorem tot13818 : totK PD2M8K2 D2M8K2.t13818 = [187343934231, 469653428496, 224244281829, 13644692975, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13819 = true := by
  decide +kernel

theorem tot13819 : totK PD2M8K2 D2M8K2.t13819 = [0, 285976315350, 499618474184, 106495175621, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
