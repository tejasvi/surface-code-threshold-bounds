import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3980 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3980 = true := by
  decide +kernel

theorem tot3980 : totK PA10K2 A10K2.t3980 = [0, 0, 487128049630, 1859942659411, 2032375709358, 522677933413, 23116349954, 0, 0, 0] := by
  decide +kernel

theorem rows3981 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3981 = true := by
  decide +kernel

theorem tot3981 : totK PA10K2 A10K2.t3981 = [0, 0, 0, 682995843073, 2046335900025, 1722070644584, 405971727165, 25734533292, 0, 0] := by
  decide +kernel

theorem rows3982 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3982 = true := by
  decide +kernel

theorem tot3982 : totK PA10K2 A10K2.t3982 = [0, 0, 384418616082, 1309754815235, 1794776187345, 1138507326379, 192493264030, 6034215561, 0, 0] := by
  decide +kernel

theorem rows3983 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3983 = true := by
  decide +kernel

theorem tot3983 : totK PA10K2 A10K2.t3983 = [0, 0, 357659149530, 1672779304541, 2101522203215, 631639355506, 32877822373, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
