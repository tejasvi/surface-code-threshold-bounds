import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12404 = true := by
  decide +kernel

theorem tot12404 : totK PD2M8K2 D2M8K2.t12404 = [0, 171045894958, 466837019441, 251293951326, 16551812995, 0, 0, 0] := by
  decide +kernel

theorem rows12405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12405 = true := by
  decide +kernel

theorem tot12405 : totK PD2M8K2 D2M8K2.t12405 = [0, 0, 246129483370, 511628055797, 137373843388, 2309606161, 0, 0] := by
  decide +kernel

theorem rows12406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12406 = true := by
  decide +kernel

theorem tot12406 : totK PD2M8K2 D2M8K2.t12406 = [0, 70541481998, 258408912299, 393447538164, 145409174883, 10740121073, 0, 0] := by
  decide +kernel

theorem rows12407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12407 = true := by
  decide +kernel

theorem tot12407 : totK PD2M8K2 D2M8K2.t12407 = [0, 174976511877, 464248185960, 250994906803, 22762265210, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
