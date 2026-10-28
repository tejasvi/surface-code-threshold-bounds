import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13488 = true := by
  decide +kernel

theorem tot13488 : totK PD2M8K2 D2M8K2.t13488 = [0, 0, 0, 304438785998, 502244029966, 94856443733, 1096505104, 0] := by
  decide +kernel

theorem rows13489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13489 = true := by
  decide +kernel

theorem tot13489 : totK PD2M8K2 D2M8K2.t13489 = [0, 0, 0, 273309936152, 497409134798, 124480633858, 3884009855, 0] := by
  decide +kernel

theorem rows13490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13490 = true := by
  decide +kernel

theorem tot13490 : totK PD2M8K2 D2M8K2.t13490 = [0, 0, 0, 166500940935, 469584231146, 203030660199, 10786488463, 0] := by
  decide +kernel

theorem rows13491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13491 = true := by
  decide +kernel

theorem tot13491 : totK PD2M8K2 D2M8K2.t13491 = [0, 0, 0, 150457178999, 445250139307, 232865610358, 18237953563, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
