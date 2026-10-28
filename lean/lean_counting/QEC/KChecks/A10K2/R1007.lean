import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4028 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4028 = true := by
  decide +kernel

theorem tot4028 : totK PA10K2 A10K2.t4028 = [0, 202983038621, 946690963578, 1842906609861, 1503295964338, 327916574573, 16283799455, 0, 0, 0] := by
  decide +kernel

theorem rows4029 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4029 = true := by
  decide +kernel

theorem tot4029 : totK PA10K2 A10K2.t4029 = [0, 462363017341, 1791710033006, 2041269891578, 647851230217, 44879053215, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4030 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4030 = true := by
  decide +kernel

theorem tot4030 : totK PA10K2 A10K2.t4030 = [0, 227979659980, 1283975746665, 2202425995753, 1180250849779, 126701362826, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4031 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4031 = true := by
  decide +kernel

theorem tot4031 : totK PA10K2 A10K2.t4031 = [0, 0, 612761359905, 2064980249461, 1916067264587, 426982474842, 13816090359, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
