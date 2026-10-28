import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12472 = true := by
  decide +kernel

theorem tot12472 : totK PD2M8K2 D2M8K2.t12472 = [0, 144979296010, 439763615848, 280413452745, 22359763919, 0, 0, 0] := by
  decide +kernel

theorem rows12473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12473 = true := by
  decide +kernel

theorem tot12473 : totK PD2M8K2 D2M8K2.t12473 = [0, 0, 206998926604, 485514595039, 175976013869, 9587713104, 0, 0] := by
  decide +kernel

theorem rows12474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12474 = true := by
  decide +kernel

theorem tot12474 : totK PD2M8K2 D2M8K2.t12474 = [0, 87978670910, 315086154855, 374878787957, 98887808907, 3462014130, 0, 0] := by
  decide +kernel

theorem rows12475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12475 = true := by
  decide +kernel

theorem tot12475 : totK PD2M8K2 D2M8K2.t12475 = [0, 158674545110, 451017423012, 268037477817, 21779019004, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
