import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6844 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6844 = true := by
  decide +kernel

theorem tot6844 : totK PA10K2 A10K2.t6844 = [0, 297281370121, 1446296240863, 2182375571850, 950269589452, 83466288351, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6845 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6845 = true := by
  decide +kernel

theorem tot6845 : totK PA10K2 A10K2.t6845 = [0, 0, 486788905016, 1814005363459, 1857117854953, 499564904323, 31306924438, 0, 0, 0] := by
  decide +kernel

theorem rows6846 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6846 = true := by
  decide +kernel

theorem tot6846 : totK PA10K2 A10K2.t6846 = [0, 444538933688, 1682951821212, 1952661506925, 696098423106, 64974644892, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6847 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6847 = true := by
  decide +kernel

theorem tot6847 : totK PA10K2 A10K2.t6847 = [0, 217510155594, 1182635906688, 2089291303755, 1195223879646, 184841550963, 6239673734, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
