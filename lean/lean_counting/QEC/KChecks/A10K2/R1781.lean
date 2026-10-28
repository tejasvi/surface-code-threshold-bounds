import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7124 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7124 = true := by
  decide +kernel

theorem tot7124 : totK PA10K2 A10K2.t7124 = [0, 0, 417058886421, 1606513450293, 2028696035767, 834168730477, 74707952681, 0, 0, 0] := by
  decide +kernel

theorem rows7125 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7125 = true := by
  decide +kernel

theorem tot7125 : totK PA10K2 A10K2.t7125 = [0, 0, 393278407993, 1681436870938, 2035454396621, 713215517066, 55848420264, 0, 0, 0] := by
  decide +kernel

theorem rows7126 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7126 = true := by
  decide +kernel

theorem tot7126 : totK PA10K2 A10K2.t7126 = [0, 0, 0, 730881046556, 2248705707995, 1599406829797, 253459546871, 6904928264, 0, 0] := by
  decide +kernel

theorem rows7127 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7127 = true := by
  decide +kernel

theorem tot7127 : totK PA10K2 A10K2.t7127 = [0, 0, 511318055732, 1885824654676, 2086383882032, 695687082661, 58540527372, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
