import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t588 = true := by
  decide +kernel

theorem tot588 : totK PD2M8K2 D2M8K2.t588 = [192376982097, 456333089479, 236056975372, 17115888737, 0, 0, 0, 0] := by
  decide +kernel

theorem rows589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t589 = true := by
  decide +kernel

theorem tot589 : totK PD2M8K2 D2M8K2.t589 = [87765346930, 415385005247, 357685780100, 38276567963, 0, 0, 0, 0] := by
  decide +kernel

theorem rows590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t590 = true := by
  decide +kernel

theorem tot590 : totK PD2M8K2 D2M8K2.t590 = [0, 287248673107, 514620049478, 103354563747, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t591 = true := by
  decide +kernel

theorem tot591 : totK PD2M8K2 D2M8K2.t591 = [175740996053, 465593434201, 250756267362, 21064364833, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
