import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows588 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t588 = true := by
  decide +kernel

theorem tot588 : totK PA10K2 A10K2.t588 = [0, 0, 557799968849, 1918265359247, 1756795743581, 393716092220, 26178842160, 0, 0, 0] := by
  decide +kernel

theorem rows589 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t589 = true := by
  decide +kernel

theorem tot589 : totK PA10K2 A10K2.t589 = [0, 0, 603764778693, 1911639562094, 1734853756891, 383874756944, 11866545492, 0, 0, 0] := by
  decide +kernel

theorem rows590 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t590 = true := by
  decide +kernel

theorem tot590 : totK PA10K2 A10K2.t590 = [0, 0, 431944447300, 1691108832156, 1794966745018, 548385780723, 50109395967, 0, 0, 0] := by
  decide +kernel

theorem rows591 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t591 = true := by
  decide +kernel

theorem tot591 : totK PA10K2 A10K2.t591 = [0, 0, 207095805940, 1419830013602, 2141165294974, 769217441992, 58344830985, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
