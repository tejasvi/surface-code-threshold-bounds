import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2844 = true := by
  decide +kernel

theorem tot2844 : totK PD2M8K2 D2M8K2.t2844 = [0, 0, 203516936693, 473091013178, 207733487854, 11867500000, 0, 0] := by
  decide +kernel

theorem rows2845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2845 = true := by
  decide +kernel

theorem tot2845 : totK PD2M8K2 D2M8K2.t2845 = [0, 65887972987, 229748072821, 398518783262, 178250705126, 7877424857, 0, 0] := by
  decide +kernel

theorem rows2846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2846 = true := by
  decide +kernel

theorem tot2846 : totK PD2M8K2 D2M8K2.t2846 = [0, 182427998068, 469581977225, 248754355073, 23089623618, 0, 0, 0] := by
  decide +kernel

theorem rows2847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2847 = true := by
  decide +kernel

theorem tot2847 : totK PD2M8K2 D2M8K2.t2847 = [0, 172679268313, 463908250186, 242472464819, 13484745446, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
