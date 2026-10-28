import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13208 = true := by
  decide +kernel

theorem tot13208 : totK PD2M8K2 D2M8K2.t13208 = [0, 0, 185508023896, 452519231085, 261074361252, 26032761090, 0, 0] := by
  decide +kernel

theorem rows13209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13209 = true := by
  decide +kernel

theorem tot13209 : totK PD2M8K2 D2M8K2.t13209 = [0, 0, 183916677782, 489505797538, 232700636800, 9348026610, 0, 0] := by
  decide +kernel

theorem rows13210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13210 = true := by
  decide +kernel

theorem tot13210 : totK PD2M8K2 D2M8K2.t13210 = [0, 0, 171455742254, 450372890980, 252895709889, 23437205167, 0, 0] := by
  decide +kernel

theorem rows13211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13211 = true := by
  decide +kernel

theorem tot13211 : totK PD2M8K2 D2M8K2.t13211 = [0, 0, 166855251761, 450701305415, 254859901985, 17616268841, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
