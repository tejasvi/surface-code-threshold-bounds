import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4196 = true := by
  decide +kernel

theorem tot4196 : totK PD2M8K2 D2M8K2.t4196 = [0, 0, 20021956556, 194245309864, 442442693098, 209478825452, 13764981515, 0] := by
  decide +kernel

theorem rows4197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4197 = true := by
  decide +kernel

theorem tot4197 : totK PD2M8K2 D2M8K2.t4197 = [0, 0, 163263222476, 446223133447, 283290656561, 29997170311, 0, 0] := by
  decide +kernel

theorem rows4198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4198 = true := by
  decide +kernel

theorem tot4198 : totK PD2M8K2 D2M8K2.t4198 = [0, 0, 203276664313, 479749728068, 221201168989, 11451703945, 0, 0] := by
  decide +kernel

theorem rows4199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4199 = true := by
  decide +kernel

theorem tot4199 : totK PD2M8K2 D2M8K2.t4199 = [0, 0, 63373019371, 295374504560, 378528592919, 170306253356, 17186218589, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
