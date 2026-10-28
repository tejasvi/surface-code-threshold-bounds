import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1780 = true := by
  decide +kernel

theorem tot1780 : totK PD2M8K2 D2M8K2.t1780 = [0, 106245156730, 414380634955, 360537968842, 37623955165, 0, 0, 0] := by
  decide +kernel

theorem rows1781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1781 = true := by
  decide +kernel

theorem tot1781 : totK PD2M8K2 D2M8K2.t1781 = [0, 180858148563, 445924776683, 254774322990, 26577308020, 0, 0, 0] := by
  decide +kernel

theorem rows1782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1782 = true := by
  decide +kernel

theorem tot1782 : totK PD2M8K2 D2M8K2.t1782 = [0, 138364426017, 444633349131, 290693267972, 23827129960, 0, 0, 0] := by
  decide +kernel

theorem rows1783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1783 = true := by
  decide +kernel

theorem tot1783 : totK PD2M8K2 D2M8K2.t1783 = [0, 0, 198621345116, 493569635550, 183804912056, 9587713104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
