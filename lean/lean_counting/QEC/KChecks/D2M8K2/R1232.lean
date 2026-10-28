import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4928 = true := by
  decide +kernel

theorem tot4928 : totK PD2M8K2 D2M8K2.t4928 = [0, 0, 196494997860, 481239034999, 218783440905, 12361366339, 0, 0] := by
  decide +kernel

theorem rows4929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4929 = true := by
  decide +kernel

theorem tot4929 : totK PD2M8K2 D2M8K2.t4929 = [0, 0, 34655881336, 318875731854, 449189234490, 92388653863, 1198073392, 0] := by
  decide +kernel

theorem rows4930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4930 = true := by
  decide +kernel

theorem tot4930 : totK PD2M8K2 D2M8K2.t4930 = [0, 0, 0, 212246292420, 475053465961, 185114807955, 8376437251, 0] := by
  decide +kernel

theorem rows4931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4931 = true := by
  decide +kernel

theorem tot4931 : totK PD2M8K2 D2M8K2.t4931 = [0, 0, 172430498672, 456063376113, 262677348484, 30547437497, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
