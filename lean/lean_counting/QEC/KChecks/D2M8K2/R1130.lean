import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4520 = true := by
  decide +kernel

theorem tot4520 : totK PD2M8K2 D2M8K2.t4520 = [0, 0, 210608836434, 485704885158, 181531398683, 7442000727, 0, 0] := by
  decide +kernel

theorem rows4521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4521 = true := by
  decide +kernel

theorem tot4521 : totK PD2M8K2 D2M8K2.t4521 = [0, 0, 188971463821, 475138812856, 211672500619, 14707859566, 0, 0] := by
  decide +kernel

theorem rows4522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4522 = true := by
  decide +kernel

theorem tot4522 : totK PD2M8K2 D2M8K2.t4522 = [0, 0, 173221005948, 478925858980, 217508780273, 9064506700, 0, 0] := by
  decide +kernel

theorem rows4523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4523 = true := by
  decide +kernel

theorem tot4523 : totK PD2M8K2 D2M8K2.t4523 = [0, 0, 88333075132, 344818926854, 379136625847, 68562802307, 1310285577, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
