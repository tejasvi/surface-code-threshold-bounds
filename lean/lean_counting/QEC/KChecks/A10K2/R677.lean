import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2708 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2708 = true := by
  decide +kernel

theorem tot2708 : totK PA10K2 A10K2.t2708 = [0, 0, 502148186112, 1847271907663, 1904761660379, 509269386552, 31768748853, 0, 0, 0] := by
  decide +kernel

theorem rows2709 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2709 = true := by
  decide +kernel

theorem tot2709 : totK PA10K2 A10K2.t2709 = [0, 482403941286, 1683584036812, 1823215780235, 695913270893, 76459811346, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2710 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2710 = true := by
  decide +kernel

theorem tot2710 : totK PA10K2 A10K2.t2710 = [0, 298064684126, 1485984277871, 2109639821603, 825934333966, 60102351277, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2711 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2711 = true := by
  decide +kernel

theorem tot2711 : totK PA10K2 A10K2.t2711 = [0, 284548233047, 1163518462760, 1910666387837, 1205879378302, 221302407274, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
