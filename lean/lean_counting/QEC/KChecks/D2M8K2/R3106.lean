import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12424 = true := by
  decide +kernel

theorem tot12424 : totK PD2M8K2 D2M8K2.t12424 = [0, 0, 283929681891, 508314867842, 111884612359, 1178750802, 0, 0] := by
  decide +kernel

theorem rows12425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12425 = true := by
  decide +kernel

theorem tot12425 : totK PD2M8K2 D2M8K2.t12425 = [0, 31911208960, 203248803220, 439028989156, 189913336512, 11991925116, 0, 0] := by
  decide +kernel

theorem rows12426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12426 = true := by
  decide +kernel

theorem tot12426 : totK PD2M8K2 D2M8K2.t12426 = [0, 174300219180, 451675268541, 250724243547, 22758451065, 0, 0, 0] := by
  decide +kernel

theorem rows12427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12427 = true := by
  decide +kernel

theorem tot12427 : totK PD2M8K2 D2M8K2.t12427 = [0, 197947874574, 459047518507, 227490496719, 16988898864, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
