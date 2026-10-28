import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4188 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4188 = true := by
  decide +kernel

theorem tot4188 : totK PA10K2 A10K2.t4188 = [27346204002, 793862664922, 2082806201095, 1547946956545, 376656991373, 25734533292, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4189 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4189 = true := by
  decide +kernel

theorem tot4189 : totK PA10K2 A10K2.t4189 = [377060897372, 1308340333578, 1762332490914, 1117804414283, 195574700343, 6034215561, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4190 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4190 = true := by
  decide +kernel

theorem tot4190 : totK PA10K2 A10K2.t4190 = [460446214129, 1828522365563, 1948290012954, 499706473664, 26521581199, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4191 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4191 = true := by
  decide +kernel

theorem tot4191 : totK PA10K2 A10K2.t4191 = [0, 833237086702, 2316226481237, 1417276026687, 141126410570, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
