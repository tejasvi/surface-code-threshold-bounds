import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11008 = true := by
  decide +kernel

theorem tot11008 : totK PD2M8K2 D2M8K2.t11008 = [28667399668, 174298488806, 415016458249, 253628504889, 22321705707, 0, 0, 0] := by
  decide +kernel

theorem rows11009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11009 = true := by
  decide +kernel

theorem tot11009 : totK PD2M8K2 D2M8K2.t11009 = [202663279768, 483844536190, 198604506644, 9848247143, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11010 = true := by
  decide +kernel

theorem tot11010 : totK PD2M8K2 D2M8K2.t11010 = [184159978963, 467512673528, 225523382962, 12534051746, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11011 = true := by
  decide +kernel

theorem tot11011 : totK PD2M8K2 D2M8K2.t11011 = [0, 282643948186, 492637964531, 106866598113, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
