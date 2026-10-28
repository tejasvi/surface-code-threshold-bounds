import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2080 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2080 = true := by
  decide +kernel

theorem tot2080 : totK PA10K2 A10K2.t2080 = [0, 474097331114, 1607678591370, 1835824953720, 862465583733, 148449648201, 6239673734, 0, 0, 0] := by
  decide +kernel

theorem rows2081 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2081 = true := by
  decide +kernel

theorem tot2081 : totK PA10K2 A10K2.t2081 = [0, 310203719009, 1485104505939, 2178380469906, 939618040462, 82384530216, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2082 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2082 = true := by
  decide +kernel

theorem tot2082 : totK PA10K2 A10K2.t2082 = [0, 0, 652020507445, 2199103239013, 1877148937535, 341696688865, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows2083 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2083 = true := by
  decide +kernel

theorem tot2083 : totK PA10K2 A10K2.t2083 = [0, 0, 315787938438, 1533137724841, 2149920764207, 802255567018, 60578866985, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
