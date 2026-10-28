import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1248 = true := by
  decide +kernel

theorem tot1248 : totK PD2M8K2 D2M8K2.t1248 = [172936612357, 449646223811, 270043640620, 21622700334, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1249 = true := by
  decide +kernel

theorem tot1249 : totK PD2M8K2 D2M8K2.t1249 = [123907010439, 434089729611, 312411031202, 36008609644, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1250 = true := by
  decide +kernel

theorem tot1250 : totK PD2M8K2 D2M8K2.t1250 = [0, 161781037774, 448274249810, 265806908047, 25265558709, 0, 0, 0] := by
  decide +kernel

theorem rows1251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1251 = true := by
  decide +kernel

theorem tot1251 : totK PD2M8K2 D2M8K2.t1251 = [37176659836, 192425291977, 433040748938, 225853009900, 11012868366, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
