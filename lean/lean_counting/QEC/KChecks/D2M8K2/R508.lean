import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2032 = true := by
  decide +kernel

theorem tot2032 : totK PD2M8K2 D2M8K2.t2032 = [0, 0, 33744608220, 219726224369, 411244059288, 178884295915, 11934365838, 0] := by
  decide +kernel

theorem rows2033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2033 = true := by
  decide +kernel

theorem tot2033 : totK PD2M8K2 D2M8K2.t2033 = [0, 0, 200612139549, 470073223495, 204918078891, 11071105621, 0, 0] := by
  decide +kernel

theorem rows2034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2034 = true := by
  decide +kernel

theorem tot2034 : totK PD2M8K2 D2M8K2.t2034 = [0, 0, 179792741300, 469847998558, 226660772129, 13176583453, 0, 0] := by
  decide +kernel

theorem rows2035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2035 = true := by
  decide +kernel

theorem tot2035 : totK PD2M8K2 D2M8K2.t2035 = [0, 0, 0, 330446061520, 440350628978, 69316186947, 1053411165, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
