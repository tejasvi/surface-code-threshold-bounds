import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4788 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4788 = true := by
  decide +kernel

theorem tot4788 : totK PA10K2 A10K2.t4788 = [0, 0, 0, 629579634434, 1938004935795, 1673188157406, 419941507949, 31690778550, 0, 0] := by
  decide +kernel

theorem rows4789 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4789 = true := by
  decide +kernel

theorem tot4789 : totK PA10K2 A10K2.t4789 = [0, 0, 0, 578656498428, 1965070968007, 1715802436062, 331180431949, 11774637377, 0, 0] := by
  decide +kernel

theorem rows4790 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4790 = true := by
  decide +kernel

theorem tot4790 : totK PA10K2 A10K2.t4790 = [0, 0, 0, 465281826316, 1864505443015, 1841706428579, 409563667513, 25454126167, 0, 0] := by
  decide +kernel

theorem rows4791 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4791 = true := by
  decide +kernel

theorem tot4791 : totK PA10K2 A10K2.t4791 = [0, 0, 0, 0, 801874090741, 2219563375267, 1266344872214, 134654259756, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
