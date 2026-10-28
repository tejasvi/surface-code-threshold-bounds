import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5668 = true := by
  decide +kernel

theorem tot5668 : totK PD2M8K2 D2M8K2.t5668 = [0, 86874248361, 307476291481, 371920629646, 103101195998, 3824247485, 0, 0] := by
  decide +kernel

theorem rows5669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5669 = true := by
  decide +kernel

theorem tot5669 : totK PD2M8K2 D2M8K2.t5669 = [0, 172057267468, 471934285711, 250089835673, 19949658790, 0, 0, 0] := by
  decide +kernel

theorem rows5670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5670 = true := by
  decide +kernel

theorem tot5670 : totK PD2M8K2 D2M8K2.t5670 = [0, 179163009487, 462446619811, 246546035023, 13811584538, 0, 0, 0] := by
  decide +kernel

theorem rows5671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5671 = true := by
  decide +kernel

theorem tot5671 : totK PD2M8K2 D2M8K2.t5671 = [0, 0, 288417837379, 489960089891, 106690834668, 1242138600, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
