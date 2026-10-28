import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12088 = true := by
  decide +kernel

theorem tot12088 : totK PD2M8K2 D2M8K2.t12088 = [0, 164670449871, 437486188485, 290509143292, 33189830053, 0, 0, 0] := by
  decide +kernel

theorem rows12089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12089 = true := by
  decide +kernel

theorem tot12089 : totK PD2M8K2 D2M8K2.t12089 = [0, 201257760517, 477820372949, 219079140622, 12366815362, 0, 0, 0] := by
  decide +kernel

theorem rows12090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12090 = true := by
  decide +kernel

theorem tot12090 : totK PD2M8K2 D2M8K2.t12090 = [0, 53304886208, 282400357025, 368867123960, 171696988122, 18574160761, 0, 0] := by
  decide +kernel

theorem rows12091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12091 = true := by
  decide +kernel

theorem tot12091 : totK PD2M8K2 D2M8K2.t12091 = [0, 0, 219676177957, 492906817196, 176578524959, 5019596775, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
