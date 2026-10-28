import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11376 = true := by
  decide +kernel

theorem tot11376 : totK PD2M8K2 D2M8K2.t11376 = [0, 188424964003, 466780028115, 238837773242, 13108638253, 0, 0, 0] := by
  decide +kernel

theorem rows11377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11377 = true := by
  decide +kernel

theorem tot11377 : totK PD2M8K2 D2M8K2.t11377 = [0, 192398864976, 478931861936, 226228946721, 14758207119, 0, 0, 0] := by
  decide +kernel

theorem rows11378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11378 = true := by
  decide +kernel

theorem tot11378 : totK PD2M8K2 D2M8K2.t11378 = [0, 179227451865, 451540666033, 260330626620, 21999437347, 0, 0, 0] := by
  decide +kernel

theorem rows11379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11379 = true := by
  decide +kernel

theorem tot11379 : totK PD2M8K2 D2M8K2.t11379 = [0, 155837405811, 456485853655, 261901710126, 18510022789, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
